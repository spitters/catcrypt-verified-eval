/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.FragmentCoverageLoop
public import Lean
public import Lean.Meta.Native

/-!
# Deciding a proposition by running the compiled fragment on the machine model

A decision procedure registered as a `DecisionProc α P` is a fragment program with a proof,
once for all inputs, that it answers `true` on the state of an input `x` exactly when `P x`.
The compiler with loops `compileProgL` of
`VerifiedEval.FragmentCompileLoop` turns the program into
`JInstr 64` code, and `encodeJBlock6` into bytes. `verifiedDecide_sound` derives `P x` from
the answer `machineAccepts` gives on those bytes and the initial machine state of `x`.

`machineAccepts` decodes a byte stream with `decodeJStream6`, runs the decoded block with
`runBlockA` and tests one register. It takes no program and no decision procedure: a
procedure enters only through its bytes and its initial state. The tactic `verified_decide d`
closes `P x` for a concrete `x` by evaluating one application of `machineAccepts` with the
compiler and asserting the result by an auxiliary axiom `machineAccepts … = true`, as
`native_decide` does, so the trusted evaluation is the evaluation of the machine model on data.
The machine-evaluation rule of the lean4lean checker does not recognise this axiom and accepts
it as stated; `verified_decide_lit` produces the axiom that rule confirms.

## Initial state

`initState L plan σ` is the physical machine state of a source state `σ`. Addresses are
counted from the arena base `2 ^ 20`, above the lowest address Linux maps
(`/proc/sys/vm/mmap_min_addr`): the sink cell is at `2 ^ 20` and cell `i` of the `k`-th
span of the layout is the little-endian word at address `2 ^ 20 + 8 * (1 + k * 2 ^ 32 + i)`.
With fewer than `2 ^ 11` spans, each shorter than `2 ^ 32` cells, every cell ends below
`2 ^ 47`, inside the user half of the x86-64 address space (`cellNo_addr_lt`). A register
plan `RegPlan` assigns a register number to each
role (`RegName`) the compiled code uses; the physical register of a scalar holds its value,
that of a span's length register its length, and that of a span's cell-0 register its
address. `blockView alloc t` reads the block-level register `n` of a physical state `t` at
`nameOf alloc n`, which relates the two states by `ARelOn` on every name.

## Checks

`planCheck L plan p` is a boolean check on the concrete program and plan: the plan's roles
and register numbers are distinct, every register number is below `16`, no temporary gets
`%rsp`, the data roles of the layout are planned, and every role the compiled code of `p`
names is planned (`FProg.rolesOK`, which follows the structure of `compileProgL`). Its
soundness lemmas give the `AllocOK` and `RenInjOn` hypotheses of
`compileProgL_bytes_correct`.

## Main definitions

* `machineAccepts`: the machine model's answer on a byte stream and an initial state.
* `stdName`, `stdLayout`: a layout with an injective register naming.
* `RegPlan`, `RegPlan.alloc`, `planCheck`: register plans and their check.
* `initMem`, `initRegs`, `initState`, `blockView`: the initial machine state of a source
  state.
* `DecisionProc`: a fragment program with its specification and side conditions.
* `verified_decide`: the tactic.

## Main results

* `machineAccepts_eq_true`: an accepting run decodes the bytes and leaves a nonzero result.
* `stdName_injective`: `stdLayout` satisfies `LayoutOK`.
* `allocOK_of_planCheck`, `renInjOn_of_planCheck`: the allocation conditions.
* `read64_initMem`, `initState_rel`: the block-level view of the initial state is related
  to the source state by `StateRel`, with pairwise disjoint cells and a disjoint sink.
* `verifiedDecide_sound`: an accepting machine run on the bytes of a registered procedure
  proves the proposition.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc regOf srcNames)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (encodeJInstr6 encodeJBlock6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeJBlock6Roundtrip (decodeJStream6)
open CatCrypt.Crypto.Optimizer.GenericRegAlloc (RenInjOn)
open CatCrypt.Crypto.Optimizer.JInstrRegAllocScoped
open CatCrypt.Crypto.Optimizer.JInstrRegAllocValidated (bNamesX)
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc (writtenNames readNames)

/-! ## The machine model's answer -/

/-- The machine model's answer on a byte stream: decode `n` instructions with
`decodeJStream6`, run them with `runBlockA` from `init`, and test register `res` of the final
state for a nonzero value; `false` when decoding fails. `verified_decide` evaluates
applications of this function only and asserts each answer by an auxiliary axiom. -/
def machineAccepts (bytes : List (BitVec 8)) (n : Nat) (init : AState) (res : String) : Bool :=
  match decodeJStream6 n bytes with
  | some blk => (runBlockA init blk).regs res != 0
  | none => false

/-- An accepting run decodes the bytes to a block that leaves a nonzero value in the result
register. -/
theorem machineAccepts_eq_true {bytes : List (BitVec 8)} {n : Nat} {init : AState}
    {res : String} (h : machineAccepts bytes n init res = true) :
    ∃ blk, decodeJStream6 n bytes = some blk ∧ (runBlockA init blk).regs res ≠ 0 := by
  unfold machineAccepts at h
  split at h
  · exact ⟨_, ‹_›, by simpa using h⟩
  · cases h

/-! ## A layout with an injective naming -/

/-- The string of `k` bars. -/
def natTag (k : Nat) : String := String.ofList (List.replicate k '|')

/-- A register name for each role: a one-letter role prefix followed by the scalar or span
name, or by the depth as a string of bars. -/
def stdName : RegName → String
  | .var x => "v" ++ x
  | .len s => "l" ++ s
  | .ptr s => "p" ++ s
  | .sink => "s"
  | .tmp k => "t" ++ natTag k
  | .gThen k => "a" ++ natTag k
  | .gElse k => "b" ++ natTag k
  | .gTag k => "c" ++ natTag k

theorem stdName_injective : Function.Injective stdName := by
  intro a b h
  have e := congrArg String.toList h
  cases a <;> cases b <;>
    simp [stdName, natTag, String.toList_append, List.replicate_inj] at e ⊢ <;>
    first | exact String.toList_inj.mp e | omega

/-- The layout with register names `stdName`, the given register scalars and the given
spans. -/
def stdLayout (scalars spans : List String) : Layout := ⟨stdName, scalars, spans⟩

theorem stdLayout_ok (scalars spans : List String) : LayoutOK (stdLayout scalars spans) :=
  stdName_injective

/-! ## Register plans -/

/-- A register plan: each listed role is held in the general-purpose register of the given
SDM number. -/
abbrev RegPlan := List (RegName × Nat)

/-- The allocation of a register plan: the name of each planned role maps to the `%rN` name
of its register number. -/
def RegPlan.alloc (L : Layout) (plan : RegPlan) : GpAlloc :=
  plan.map fun rk => (L.name rk.1, regName rk.2)

/-- The role is planned. -/
def RegPlan.has (plan : RegPlan) (r : RegName) : Bool := decide (r ∈ plan.map Prod.fst)

/-- The role is a temporary. -/
def RegName.isTmp : RegName → Bool
  | .tmp _ => true
  | _ => false

/-- The plan assigns distinct registers to distinct roles, lists each role once, uses
register numbers below `16`, and gives no temporary register `4` (`%rsp`). -/
def RegPlan.wellFormed (plan : RegPlan) : Bool :=
  decide (plan.map Prod.fst).Nodup && decide (plan.map Prod.snd).Nodup &&
    plan.all fun rk => decide (rk.2 < 16) && !(rk.1.isTmp && rk.2 == 4)

theorem gpNum_regName (k : Nat) (hk : k < 16) : gpNum (regName k) = k := by
  interval_cases k <;> rfl

theorem gpNum_eq_four {s : String} (h : gpNum s = 4) : s = "%rsp" := by
  unfold gpNum at h
  split at h <;> first | rfl | omega

theorem lookup_eq_of_mem {β : Type} (l : List (String × β)) (hl : (l.map Prod.fst).Nodup)
    {a : String} {b : β} (h : (a, b) ∈ l) : l.lookup a = some b := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    obtain ⟨a', b'⟩ := p
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hl
    rcases List.mem_cons.mp h with e | h'
    · cases e; simp [List.lookup]
    · have hne : a ≠ a' := fun e => hl.1 ⟨(a, b), h', e⟩
      simp [List.lookup, show (a == a') = false from by simpa using hne, ih hl.2 h']

theorem lookup_eq_none {β : Type} (l : List (String × β)) {a : String}
    (h : ∀ p ∈ l, p.1 ≠ a) : l.lookup a = none := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨a', b'⟩ := p
    have hne : a ≠ a' := fun e => h _ List.mem_cons_self e.symm
    simp only [List.lookup, show (a == a') = false from by simpa using hne]
    exact ih fun q hq => h q (List.mem_cons_of_mem _ hq)

section Plan

variable {L : Layout} {plan : RegPlan}

theorem RegPlan.wellFormed_spec (h : plan.wellFormed = true) :
    (plan.map Prod.fst).Nodup ∧ (plan.map Prod.snd).Nodup ∧
      ∀ rk ∈ plan, rk.2 < 16 ∧ (rk.1.isTmp = true → rk.2 ≠ 4) := by
  simp only [RegPlan.wellFormed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne] at h
  refine ⟨h.1.1, h.1.2, fun rk hrk => ⟨(h.2 rk hrk).1, fun ht => ?_⟩⟩
  rcases (h.2 rk hrk).2 with h' | h'
  · simp [ht] at h'
  · exact h'

theorem RegPlan.has_iff {r : RegName} : plan.has r = true ↔ ∃ k, (r, k) ∈ plan := by
  simp [RegPlan.has]

theorem RegPlan.regOf_alloc (hL : LayoutOK L) (hw : plan.wellFormed = true) {r : RegName}
    {k : Nat} (h : (r, k) ∈ plan) : regOf (plan.alloc L) (L.name r) = regName k := by
  have hn : ((plan.alloc L).map Prod.fst).Nodup := by
    have e : (plan.alloc L).map Prod.fst = (plan.map Prod.fst).map L.name := by
      simp [RegPlan.alloc, Function.comp_def]
    rw [e]
    exact (RegPlan.wellFormed_spec hw).1.map hL
  have hm : (L.name r, regName k) ∈ plan.alloc L := List.mem_map.mpr ⟨(r, k), h, rfl⟩
  simp [regOf, lookup_eq_of_mem _ hn hm]

theorem RegPlan.nameOf_alloc (hL : LayoutOK L) (hw : plan.wellFormed = true) {r : RegName}
    {k : Nat} (h : (r, k) ∈ plan) : nameOf (plan.alloc L) (L.name r) = regName k := by
  have hk := ((RegPlan.wellFormed_spec hw).2.2 _ h).1
  simp only [nameOf, RegPlan.regOf_alloc hL hw h, gpNum_regName k hk]

theorem RegPlan.eq_of_regName (hw : plan.wellFormed = true) {r r' : RegName} {k k' : Nat}
    (h : (r, k) ∈ plan) (h' : (r', k') ∈ plan) (e : regName k = regName k') : r = r' := by
  obtain ⟨_, hsnd, hlt⟩ := RegPlan.wellFormed_spec hw
  have hk : k = k' := by
    rw [← gpNum_regName k (hlt _ h).1, ← gpNum_regName k' (hlt _ h').1, e]
  subst hk
  have := List.inj_on_of_nodup_map hsnd h h' rfl
  simpa using this

theorem allocOK_of_wellFormed (hL : LayoutOK L) (hw : plan.wellFormed = true) :
    AllocOK L (plan.alloc L) where
  tmp_ne_rsp k := by
    by_cases hk : ∃ m, (RegName.tmp k, m) ∈ plan
    · obtain ⟨m, hm⟩ := hk
      obtain ⟨hlt, hne⟩ := (RegPlan.wellFormed_spec hw).2.2 _ hm
      rw [RegPlan.regOf_alloc hL hw hm, gpNum_regName m hlt]
      exact hne rfl
    · have hnone : (plan.alloc L).lookup (L.name (.tmp k)) = none := by
        refine lookup_eq_none _ fun p hp e => hk ?_
        obtain ⟨⟨r, m⟩, hrm, rfl⟩ := List.mem_map.mp hp
        exact ⟨m, (hL e) ▸ hrm⟩
      intro h4
      have e := congrArg String.toList (gpNum_eq_four h4)
      simp [regOf, hnone, String.toList_append] at e

/-- Every name in `ns` is the name of a planned role. -/
def PlannedNames (L : Layout) (plan : RegPlan) (ns : List String) : Prop :=
  ∀ n ∈ ns, ∃ r, plan.has r = true ∧ L.name r = n

theorem renInjOn_of_planned (hL : LayoutOK L) (hw : plan.wellFormed = true) {ns : List String}
    (h : PlannedNames L plan ns) : RenInjOn ns (nameOf (plan.alloc L)) := by
  intro a ha b hb e
  obtain ⟨r, hr, rfl⟩ := h a ha
  obtain ⟨r', hr', rfl⟩ := h b hb
  obtain ⟨k, hk⟩ := RegPlan.has_iff.mp hr
  obtain ⟨k', hk'⟩ := RegPlan.has_iff.mp hr'
  rw [RegPlan.nameOf_alloc hL hw hk, RegPlan.nameOf_alloc hL hw hk'] at e
  rw [RegPlan.eq_of_regName hw hk hk' e]

end Plan

/-! ## The roles the compiled code names -/

section Roles

variable (inR : RegName → Bool)

/-- The seven roles a span read at temporary `d` of span `t` names are accepted. -/
def getOK (t : String) (d : Nat) : Bool :=
  inR (.tmp d) && inR (.tmp (d + 1)) && inR (.tmp (d + 2)) && inR (.tmp (d + 3)) &&
    inR .sink && inR (.len t) && inR (.ptr t)

/-- Every role the code of an expression at temporary `d` names is accepted, following the
structure of `compileExpr`. -/
def FExpr.rolesOK (d : Nat) : FExpr → Bool
  | .var x => inR (.tmp d) && inR (.var x)
  | .lit _ => inR (.tmp d)
  | .bin op a b =>
      if op.isCompare then
        a.rolesOK d && b.rolesOK (d + 1) && inR (.tmp d) && inR (.tmp (d + 1)) &&
          inR (.tmp (d + 2))
      else if op.isShift then a.rolesOK d && inR (.tmp d) && inR (.tmp (d + 1))
      else a.rolesOK d && b.rolesOK (d + 1) && inR (.tmp d) && inR (.tmp (d + 1))
  | .not a => a.rolesOK d && inR (.tmp d) && inR (.tmp (d + 1))
  | .spanLen t => inR (.tmp d) && inR (.len t)
  | .spanGet t i => i.rolesOK d && getOK inR t d
  | .tagOf t => getOK inR t d
  | .payload t => getOK inR t d

/-- The roles of the guarded assignment of `x` under guard `g` are accepted. -/
def assignOK (g : RegName) (x : String) (e : FExpr) : Bool :=
  e.rolesOK inR 0 && inR (.tmp 0) && inR (.tmp 1) && inR g && inR (.var x)

mutual

/-- Every role the code with loops of a statement at depth `k` under guard `g` names is
accepted, following the structure of `compileStmtL`. -/
def FStmt.rolesOK : Nat → RegName → FStmt → Bool
  | _, _, .skip => true
  | k, g, .seq a b => a.rolesOK k g && b.rolesOK k g
  | _, g, .assign x e => assignOK inR g x e
  | _, g, .spanSet t i v =>
      v.rolesOK inR 0 && i.rolesOK inR 1 && getOK inR t 1 && inR (.tmp 0) && inR g
  | k, g, .ite c a b =>
      c.rolesOK inR 0 && inR (.tmp 0) && inR (.tmp 1) && inR g && inR (.gThen (k + 1)) &&
        inR (.gElse (k + 1)) && a.rolesOK (k + 1) (.gThen (k + 1)) &&
        b.rolesOK (k + 1) (.gElse (k + 1))
  | k, g, .matchTag t arms dflt =>
      getOK inR t 0 && inR (.gTag (k + 1)) && inR (.gElse (k + 1)) && inR g &&
        FStmt.rolesOKArms k arms && dflt.rolesOK (k + 1) (.gElse (k + 1))
  | k, g, .forLit i _ body => assignOK inR g i (.lit 0) && body.rolesOK k g
  | k, g, .forLen i t body =>
      inR (.tmp 0) && inR (.len t) && inR (.gThen (k + 1)) && inR g &&
        assignOK inR (.gThen (k + 1)) i (.lit 0) && body.rolesOK (k + 1) (.gThen (k + 1))

/-- Every role the code of the arms of a `matchTag` at depth `k` names is accepted. -/
def FStmt.rolesOKArms (k : Nat) : List (Nat × FStmt) → Bool
  | [] => true
  | (_, b) :: rest =>
      inR (.tmp 0) && inR (.tmp 1) && inR (.gTag (k + 1)) && inR (.gThen (k + 1)) &&
        inR (.gElse (k + 1)) && b.rolesOK (k + 1) (.gThen (k + 1)) && FStmt.rolesOKArms k rest

end

/-- Every role the compiled program with loops names is accepted, and so is temporary 0. -/
def FProg.rolesOK (p : FProg) : Bool :=
  inR (.gThen 0) && inR (.tmp 0) && p.body.rolesOK inR 0 (.gThen 0) && p.result.rolesOK inR 0

variable (L : Layout)

/-- Every register name of the block is the name of an accepted role. -/
def NamesIn (c : List (JInstr 64)) : Prop :=
  ∀ n ∈ blockNamesXsym c, ∃ r, inR r = true ∧ L.name r = n

variable {inR L}

theorem namesIn_nil : NamesIn inR L [] := by
  simp [NamesIn, blockNamesXsym]

theorem namesIn_append {a b : List (JInstr 64)} :
    NamesIn inR L (a ++ b) ↔ NamesIn inR L a ∧ NamesIn inR L b := by
  simp only [NamesIn, blockNamesXsym, List.flatMap_append, List.mem_append]
  constructor
  · intro h; exact ⟨fun n hn => h n (Or.inl hn), fun n hn => h n (Or.inr hn)⟩
  · rintro ⟨ha, hb⟩ n (hn | hn)
    exacts [ha n hn, hb n hn]

theorem namesIn_cons {i : JInstr 64} {c : List (JInstr 64)} :
    NamesIn inR L (i :: c) ↔ NamesIn inR L [i] ∧ NamesIn inR L c := by
  rw [← namesIn_append]; rfl

theorem nm_of {r : RegName} (h : inR r = true) : ∃ r', inR r' = true ∧ L.name r' = L.name r :=
  ⟨r, h, rfl⟩

/-- Names of short instruction lists: unfold the name accessors to a conjunction of
membership goals and close each by a hypothesis. -/
syntax "names_tac" : tactic
macro_rules
  | `(tactic| names_tac) =>
    `(tactic| (simp only [NamesIn, blockNamesXsym, List.flatMap_cons, List.flatMap_nil,
        bNamesXsym, bNamesX, writtenNames, readNames, srcNames, List.append_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, tR, and_true] <;>
      (repeat' apply And.intro) <;> exact nm_of (by assumption)))

theorem maskCode_names (w : FWidth) (d : Nat) (h0 : inR (.tmp d) = true)
    (h1 : inR (.tmp (d + 1)) = true) : NamesIn inR L (maskCode L w d) := by
  simp only [maskCode]; names_tac

theorem getCode_names (t : String) (d : Nat) (h : getOK inR t d = true) :
    NamesIn inR L (getCode L t d) := by
  simp only [getOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, hs⟩, hl⟩, hp⟩ := h
  simp only [getCode, selCode]; names_tac

theorem cmpCode_names (op : FBinop) (d : Nat) (h0 : inR (.tmp d) = true)
    (h1 : inR (.tmp (d + 1)) = true) (h2 : inR (.tmp (d + 2)) = true) :
    NamesIn inR L (cmpCode L op d) := by
  cases op <;> simp only [cmpCode] <;> first | exact namesIn_nil | names_tac

theorem notCode_names (d : Nat) (h0 : inR (.tmp d) = true)
    (h1 : inR (.tmp (d + 1)) = true) : NamesIn inR L (notCode L d) := by
  simp only [notCode]; names_tac

theorem arithInstr_names (op : FBinop) (d : String) (o : JOperand)
    (hd : ∃ r, inR r = true ∧ L.name r = d)
    (ho : ∀ n, o = .reg n → ∃ r, inR r = true ∧ L.name r = n) :
    NamesIn inR L [arithInstr op d o] := by
  have ho' : ∀ n ∈ srcNames o, ∃ r, inR r = true ∧ L.name r = n := by
    intro n hn
    cases o with
    | reg m => simp only [srcNames, List.mem_singleton] at hn; exact ho n (hn ▸ rfl)
    | imm v => simp [srcNames] at hn
  intro n hn
  simp only [blockNamesXsym, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hn
  have key : n = d ∨ n ∈ srcNames o := by
    cases op <;>
      simp only [arithInstr, bNamesXsym, bNamesX, writtenNames, readNames, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hn <;> tauto
  rcases key with rfl | hn
  exacts [hd, ho' _ hn]

theorem compileExpr_names (Γ : String → FWidth) :
    ∀ (e : FExpr) (d : Nat), e.rolesOK inR d = true → NamesIn inR L (compileExpr L Γ d e)
  | .var x, d, h => by
      simp only [FExpr.rolesOK, Bool.and_eq_true] at h
      obtain ⟨h0, hx⟩ := h
      simp only [compileExpr]; names_tac
  | .lit n, d, h => by
      simp only [FExpr.rolesOK] at h
      simp only [compileExpr]; names_tac
  | .bin op a b, d, h => by
      simp only [FExpr.rolesOK] at h
      simp only [compileExpr]
      by_cases hc : op.isCompare = true
      · simp only [hc, ite_true, Bool.and_eq_true] at h ⊢
        obtain ⟨⟨⟨⟨ha, hb⟩, h0⟩, h1⟩, h2⟩ := h
        exact namesIn_append.mpr ⟨namesIn_append.mpr ⟨compileExpr_names Γ a d ha,
          compileExpr_names Γ b (d + 1) hb⟩, cmpCode_names op d h0 h1 h2⟩
      · simp only [hc, Bool.false_eq_true, ite_false] at h ⊢
        by_cases hs : op.isShift = true
        · simp only [hs, ite_true, Bool.and_eq_true] at h ⊢
          obtain ⟨⟨ha, h0⟩, h1⟩ := h
          split
          · refine namesIn_append.mpr ⟨namesIn_append.mpr ⟨compileExpr_names Γ a d ha, ?_⟩,
              maskCode_names _ d h0 h1⟩
            exact arithInstr_names op _ _ (nm_of h0) (fun n hn => by cases hn)
          · exact namesIn_nil
        · simp only [hs, Bool.false_eq_true, ite_false, Bool.and_eq_true] at h ⊢
          obtain ⟨⟨⟨ha, hb⟩, h0⟩, h1⟩ := h
          refine namesIn_append.mpr ⟨namesIn_append.mpr ⟨namesIn_append.mpr
            ⟨compileExpr_names Γ a d ha, compileExpr_names Γ b (d + 1) hb⟩, ?_⟩,
            maskCode_names _ d h0 h1⟩
          exact arithInstr_names op _ _ (nm_of h0) (fun n hn => by cases hn; exact nm_of h1)
  | .not a, d, h => by
      simp only [FExpr.rolesOK, Bool.and_eq_true] at h
      obtain ⟨⟨ha, h0⟩, h1⟩ := h
      simp only [compileExpr]
      exact namesIn_append.mpr ⟨compileExpr_names Γ a d ha, notCode_names d h0 h1⟩
  | .spanLen t, d, h => by
      simp only [FExpr.rolesOK, Bool.and_eq_true] at h
      obtain ⟨h0, hl⟩ := h
      simp only [compileExpr]; names_tac
  | .spanGet t i, d, h => by
      simp only [FExpr.rolesOK, Bool.and_eq_true] at h
      simp only [compileExpr]
      exact namesIn_append.mpr ⟨compileExpr_names Γ i d h.1, getCode_names t d h.2⟩
  | .tagOf t, d, h => by
      simp only [FExpr.rolesOK] at h
      have h0 : inR (.tmp d) = true := by simp only [getOK, Bool.and_eq_true] at h; exact h.1.1.1.1.1.1
      simp only [compileExpr]
      exact namesIn_cons.mpr ⟨by names_tac, getCode_names t d h⟩
  | .payload t, d, h => by
      simp only [FExpr.rolesOK] at h
      have h0 : inR (.tmp d) = true := by simp only [getOK, Bool.and_eq_true] at h; exact h.1.1.1.1.1.1
      simp only [compileExpr]
      exact namesIn_cons.mpr ⟨by names_tac, getCode_names t d h⟩

theorem assignCode_names (Γ : String → FWidth) (g : RegName) (x : String) (e : FExpr)
    (h : assignOK inR g x e = true) : NamesIn inR L (assignCode L Γ g x e) := by
  simp only [assignOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨he, h0⟩, h1⟩, hg⟩, hx⟩ := h
  simp only [assignCode]
  refine namesIn_append.mpr ⟨namesIn_append.mpr ⟨compileExpr_names Γ e 0 he,
    maskCode_names _ 0 h0 h1⟩, ?_⟩
  names_tac

theorem loopVarCode_names (g : RegName) (i : String) (j : Nat)
    (h : assignOK inR g i (.lit 0) = true) : NamesIn inR L (loopVarCode L g i j) := by
  simp only [assignOK, FExpr.rolesOK, Bool.and_eq_true] at h
  exact assignCode_names _ g i (.lit j) (by simp [assignOK, FExpr.rolesOK, h])

theorem unrollLit_names (g : RegName) (i : String) (c : List (JInstr 64))
    (hv : assignOK inR g i (.lit 0) = true) (hc : NamesIn inR L c) :
    ∀ n, NamesIn inR L (unrollLit L g i c n)
  | 0 => namesIn_nil
  | n + 1 => by
      simp only [unrollLit]
      exact namesIn_append.mpr ⟨unrollLit_names g i c hv hc n,
        namesIn_append.mpr ⟨loopVarCode_names g i n hv, hc⟩⟩

theorem unrollLen_names (g : RegName) (k : Nat) (i t : String) (c : List (JInstr 64))
    (hgd : inR (.tmp 0) = true ∧ inR (.len t) = true ∧ inR (.gThen (k + 1)) = true ∧
      inR g = true)
    (hv : assignOK inR (.gThen (k + 1)) i (.lit 0) = true) (hc : NamesIn inR L c) :
    ∀ m, NamesIn inR L (unrollLen L g k i t c m)
  | 0 => namesIn_nil
  | m + 1 => by
      obtain ⟨h0, hl, hG, hg⟩ := hgd
      simp only [unrollLen]
      refine namesIn_append.mpr ⟨unrollLen_names g k i t c ⟨h0, hl, hG, hg⟩ hv hc m,
        namesIn_append.mpr ⟨namesIn_append.mpr ⟨?_, loopVarCode_names _ i m hv⟩, hc⟩⟩
      simp only [lenGuard]; names_tac

mutual

theorem compileStmtL_names (Γ : String → FWidth) (cap : String → Nat) :
    ∀ (st : FStmt) (k : Nat) (g : RegName), st.rolesOK inR k g = true →
      NamesIn inR L (compileStmtL L Γ cap k g st)
  | .skip, _, _, _ => by simp only [compileStmtL]; exact namesIn_nil
  | .seq a b, k, g, h => by
      simp only [FStmt.rolesOK, Bool.and_eq_true] at h
      simp only [compileStmtL]
      exact namesIn_append.mpr ⟨compileStmtL_names Γ cap a k g h.1,
        compileStmtL_names Γ cap b k g h.2⟩
  | .assign x e, _, g, h => by
      simp only [FStmt.rolesOK] at h
      simp only [compileStmtL]
      exact assignCode_names Γ g x e h
  | .spanSet t i v, _, g, h => by
      simp only [FStmt.rolesOK, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨hv, hi⟩, hget⟩, h0⟩, hg⟩ := h
      have hget' := hget
      simp only [getOK, Bool.and_eq_true] at hget'
      obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hs⟩, hl⟩, hp⟩ := hget'
      simp only [compileStmtL, setCode]
      refine namesIn_append.mpr ⟨namesIn_append.mpr ⟨namesIn_append.mpr ⟨namesIn_append.mpr
        ⟨compileExpr_names Γ v 0 hv, maskCode_names _ 0 h0 h1⟩, compileExpr_names Γ i 1 hi⟩,
        ?_⟩, ?_⟩
      · simp only [selCode]; names_tac
      · names_tac
  | .ite c a b, k, g, h => by
      simp only [FStmt.rolesOK, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨hc, h0⟩, h1⟩, hg⟩, hT⟩, hE⟩, ha⟩, hb⟩ := h
      simp only [compileStmtL]
      refine namesIn_append.mpr ⟨namesIn_append.mpr ⟨namesIn_append.mpr
        ⟨compileExpr_names Γ c 0 hc, ?_⟩, compileStmtL_names Γ cap a _ _ ha⟩,
        compileStmtL_names Γ cap b _ _ hb⟩
      simp only [iteGuards]; names_tac
  | .matchTag t arms dflt, k, g, h => by
      simp only [FStmt.rolesOK, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨hget, hTg⟩, hE⟩, hg⟩, harms⟩, hd⟩ := h
      have h0 : inR (.tmp 0) = true := by
        simp only [getOK, Bool.and_eq_true] at hget; exact hget.1.1.1.1.1.1
      simp only [compileStmtL]
      refine namesIn_append.mpr ⟨namesIn_append.mpr ⟨?_, compileArmsL_names Γ cap arms k harms⟩,
        compileStmtL_names Γ cap dflt _ _ hd⟩
      simp only [matchPrologue]
      refine namesIn_append.mpr ⟨namesIn_cons.mpr ⟨by names_tac, getCode_names t 0 hget⟩, ?_⟩
      names_tac
  | .forLit i n body, k, g, h => by
      simp only [FStmt.rolesOK, Bool.and_eq_true] at h
      simp only [compileStmtL]
      exact unrollLit_names g i _ h.1 (compileStmtL_names Γ cap body k g h.2) n
  | .forLen i t body, k, g, h => by
      simp only [FStmt.rolesOK, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨h0, hl⟩, hG⟩, hg⟩, hv⟩, hb⟩ := h
      simp only [compileStmtL]
      exact unrollLen_names g k i t _ ⟨h0, hl, hG, hg⟩ hv
        (compileStmtL_names Γ cap body _ _ hb) (cap t)

theorem compileArmsL_names (Γ : String → FWidth) (cap : String → Nat) :
    ∀ (arms : List (Nat × FStmt)) (k : Nat), FStmt.rolesOKArms inR k arms = true →
      NamesIn inR L (compileArmsL L Γ cap k arms)
  | [], _, _ => by simp only [compileArmsL]; exact namesIn_nil
  | (tag, b) :: rest, k, h => by
      simp only [FStmt.rolesOKArms, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, hTg⟩, hT⟩, hE⟩, hb⟩, hr⟩ := h
      simp only [compileArmsL]
      refine namesIn_append.mpr ⟨namesIn_append.mpr ⟨?_, compileStmtL_names Γ cap b _ _ hb⟩,
        compileArmsL_names Γ cap rest k hr⟩
      simp only [armGuards]; names_tac

end

theorem compileProgL_names (cap : String → Nat) (p : FProg) (h : p.rolesOK inR = true) :
    ∀ n ∈ tR L 0 :: blockNamesXsym (compileProgL L cap p), ∃ r, inR r = true ∧ L.name r = n := by
  simp only [FProg.rolesOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hG, h0⟩, hb⟩, hr⟩ := h
  have hc : NamesIn inR L (compileProgL L cap p) := by
    simp only [compileProgL, List.cons_append]
    refine namesIn_cons.mpr ⟨by names_tac, namesIn_append.mpr
      ⟨compileStmtL_names p.widths cap p.body 0 _ hb, compileExpr_names p.widths p.result 0 hr⟩⟩
  intro n hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact nm_of h0
  · exact hc n hn

end Roles

/-! ## The plan check -/

/-- The boolean check on a register plan for a program: the plan is well formed, it plans
the register of every scalar of the layout, the length and cell-0 registers of every span of
the layout, and the sink register, the layout has fewer than `2 ^ 11` spans, and every role
the compiled program names is planned. -/
def planCheck (L : Layout) (plan : RegPlan) (p : FProg) : Bool :=
  plan.wellFormed && L.scalars.all (fun x => plan.has (.var x)) &&
    L.spans.all (fun t => plan.has (.len t) && plan.has (.ptr t)) && plan.has .sink &&
    decide (L.spans.length < 2 ^ 11) && p.rolesOK plan.has

section PlanCheck

variable {L : Layout} {plan : RegPlan} {p : FProg}

theorem planCheck_spec (h : planCheck L plan p = true) :
    plan.wellFormed = true ∧ (∀ x ∈ L.scalars, plan.has (.var x) = true) ∧
      (∀ t ∈ L.spans, plan.has (.len t) = true ∧ plan.has (.ptr t) = true) ∧
      plan.has .sink = true ∧ L.spans.length < 2 ^ 11 ∧ p.rolesOK plan.has = true := by
  simp only [planCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem allocOK_of_planCheck (hL : LayoutOK L) (h : planCheck L plan p = true) :
    AllocOK L (plan.alloc L) :=
  allocOK_of_wellFormed hL (planCheck_spec h).1

theorem renInjOn_of_planCheck (hL : LayoutOK L) (h : planCheck L plan p = true)
    (cap : String → Nat) :
    RenInjOn (tR L 0 :: blockNamesXsym (compileProgL L cap p)) (nameOf (plan.alloc L)) :=
  renInjOn_of_planned hL (planCheck_spec h).1
    (compileProgL_names cap p (planCheck_spec h).2.2.2.2.2)

end PlanCheck

/-! ## The initial machine state -/

/-- Cells per span in the address map. -/
def spanStride : Nat := 2 ^ 32

/-- The cell number of the sink: address `2 ^ 20`, eight bytes per cell. -/
def arenaCell : Nat := 2 ^ 17

/-- The sink address, `8 * arenaCell = 2 ^ 20`. -/
def sinkAddr : BitVec 64 := BitVec.ofNat 64 (8 * arenaCell)

/-- The address of cell 0 of span `t`: cell number `arenaCell + k * 2 ^ 32 + 1` for the
position `k` of `t` in the layout's spans, eight bytes per cell. -/
def spanBase (L : Layout) (t : String) : BitVec 64 :=
  BitVec.ofNat 64 (8 * (arenaCell + L.spans.idxOf t * spanStride + 1))

/-- The value of each data role in the initial state: a scalar's value, a span's length, the
address of a span's cell 0, the sink address; `0` for every other role. -/
def roleVal (L : Layout) (σ : FState) : RegName → BitVec 64
  | .var x => σ.scalars x
  | .len t => BitVec.ofNat 64 (σ.bufs t).length
  | .ptr t => spanBase L t
  | .sink => sinkAddr
  | _ => 0

/-- The value of cell number `c`: for `c > arenaCell`, with `c' = c - arenaCell - 1`, cell
`c' % 2 ^ 32` of the span at position `c' / 2 ^ 32`, when both exist. -/
def cellAt (L : Layout) (σ : FState) (c : Nat) : Option (BitVec 64) :=
  if c ≤ arenaCell then none
  else match L.spans[(c - arenaCell - 1) / spanStride]? with
    | some t => (σ.bufs t)[(c - arenaCell - 1) % spanStride]?
    | none => none

/-- The initial byte memory: the byte at address `a` is the byte of the cell containing `a`,
little-endian, and `0` outside every cell. -/
def initMem (L : Layout) (σ : FState) : AMem := fun a =>
  match cellAt L σ (a.toNat / 8) with
  | some v => write64 (fun _ => 0) (BitVec.ofNat 64 (8 * (a.toNat / 8))) v a
  | none => 0

/-- The initial register file: the register of each planned role holds `roleVal`, and every
other register holds `0`. -/
def initRegs (L : Layout) (plan : RegPlan) (σ : FState) : String → BitVec 64 := fun r =>
  match plan.find? (fun rk => regName rk.2 == r) with
  | some rk => roleVal L σ rk.1
  | none => 0

/-- The initial physical machine state of a source state. -/
def initState (L : Layout) (plan : RegPlan) (σ : FState) : AState :=
  { regs := initRegs L plan σ, mem := initMem L σ }

/-- The block-level view of a physical state: block-level register `n` is physical register
`nameOf alloc n`. -/
def blockView (alloc : GpAlloc) (t : AState) : AState :=
  { regs := fun n => t.regs (nameOf alloc n), flags := t.flags, mem := t.mem }

theorem aRelOn_blockView (ns : List String) (alloc : GpAlloc) (t : AState) :
    ARelOn ns (nameOf alloc) t (blockView alloc t) :=
  ⟨fun _ _ => rfl, rfl, rfl⟩

theorem read64_congr {m m' : AMem} {a : BitVec 64}
    (h : ∀ j < 8, m (a + BitVec.ofNat 64 j) = m' (a + BitVec.ofNat 64 j)) :
    read64 m a = read64 m' a := by
  have h0 := h 0 (by decide)
  simp only [BitVec.add_zero] at h0
  simp only [read64, h0, h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide)]

section Init

variable {L : Layout} {plan : RegPlan} {σ : FState}

theorem initRegs_regName (hw : plan.wellFormed = true) {r : RegName} {k : Nat}
    (h : (r, k) ∈ plan) : initRegs L plan σ (regName k) = roleVal L σ r := by
  unfold initRegs
  split
  · rename_i rk hf
    have hp := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    simp only [beq_iff_eq] at hp
    rw [RegPlan.eq_of_regName hw hm h hp]
  · rename_i hf
    exact absurd (List.find?_eq_none.mp hf (r, k) h) (by simp)

/-- The cell number of cell `i` of span `t`. -/
def cellNo (L : Layout) (t : String) (i : Nat) : Nat :=
  i + L.spans.idxOf t * spanStride + 1 + arenaCell

theorem cellNo_lt {t : String} {i : Nat} (hn : L.spans.length < 2 ^ 11) (ht : t ∈ L.spans)
    (hi : i < spanStride) : cellNo L t i < 2 ^ 44 := by
  have := List.idxOf_lt_length_iff.mpr ht
  simp only [cellNo, spanStride, arenaCell] at hi ⊢
  have : L.spans.idxOf t * 2 ^ 32 < 2 ^ 11 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right (by omega) (by decide)
  omega

/-- Every cell lies in `[2 ^ 20, 2 ^ 47)`: above the lowest address Linux maps and inside the
user half of the x86-64 address space. -/
theorem cellNo_addr_lt {t : String} {i : Nat} (hn : L.spans.length < 2 ^ 11) (ht : t ∈ L.spans)
    (hi : i < spanStride) : 2 ^ 20 < 8 * cellNo L t i ∧ 8 * cellNo L t i + 8 ≤ 2 ^ 47 := by
  have := cellNo_lt hn ht hi
  constructor
  · simp only [cellNo, arenaCell]; omega
  · omega

theorem cellAddr_spanBase (t : String) (i : Nat) :
    cellAddr (spanBase L t) i = BitVec.ofNat 64 (8 * cellNo L t i) := by
  simp only [cellAddr, spanBase]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_add_ofNat]
  congr 1
  simp only [cellNo]
  ring

theorem toNat_ofNat_of_lt {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem toNat_sub_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 b - BitVec.ofNat 64 a).toNat = if a ≤ b then b - a else 2 ^ 64 - a + b := by
  rw [BitVec.toNat_sub, toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb]
  split
  · rw [show 2 ^ 64 - a + b = (b - a) + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem cellAt_cellNo {t : String} {i : Nat} (ht : t ∈ L.spans)
    (hi : i < (σ.bufs t).length) (hs : (σ.bufs t).length < spanStride) :
    cellAt L σ (cellNo L t i) = some (σ.bufs t)[i] := by
  have hB : 0 < spanStride := by decide
  have hsub : cellNo L t i - arenaCell - 1 = i + L.spans.idxOf t * spanStride := by
    simp only [cellNo]; omega
  have hk : (cellNo L t i - arenaCell - 1) / spanStride = L.spans.idxOf t := by
    rw [hsub, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hj : (cellNo L t i - arenaCell - 1) % spanStride = i := by
    rw [hsub, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  simp only [cellAt, show ¬ cellNo L t i ≤ arenaCell by simp only [cellNo]; omega, ite_false, hk,
    List.getElem?_idxOf ht, hj, List.getElem?_eq_getElem hi]

theorem initMem_of_cellAt {a : BitVec 64} {v : BitVec 64} (h : cellAt L σ (a.toNat / 8) = some v) :
    initMem L σ a = write64 (fun _ => 0) (BitVec.ofNat 64 (8 * (a.toNat / 8))) v a := by
  unfold initMem
  rw [h]

theorem read64_initMem {t : String} {i : Nat} (hn : L.spans.length < 2 ^ 11) (ht : t ∈ L.spans)
    (hi : i < (σ.bufs t).length) (hs : (σ.bufs t).length < spanStride) :
    read64 (initMem L σ) (cellAddr (spanBase L t) i) = (σ.bufs t)[i] := by
  rw [cellAddr_spanBase]
  have hc := cellNo_lt hn ht (by omega : i < spanStride)
  rw [← read64_write64_same (fun _ => 0) (BitVec.ofNat 64 (8 * cellNo L t i)) (σ.bufs t)[i]]
  apply read64_congr
  intro j hj
  have hdiv : (BitVec.ofNat 64 (8 * cellNo L t i) + BitVec.ofNat 64 j).toNat / 8 =
      cellNo L t i := by
    rw [BitVec.ofNat_add_ofNat, toNat_ofNat_of_lt (by omega)]
    omega
  have hcell : cellAt L σ ((BitVec.ofNat 64 (8 * cellNo L t i) + BitVec.ofNat 64 j).toNat / 8) =
      some (σ.bufs t)[i] := by
    rw [hdiv]; exact cellAt_cellNo ht hi hs
  rw [initMem_of_cellAt hcell, hdiv]

theorem disjoint8_ofNat {c c' : Nat} (hc : c < 2 ^ 49) (hc' : c' < 2 ^ 49) (hne : c ≠ c') :
    Disjoint8 (BitVec.ofNat 64 (8 * c)) (BitVec.ofNat 64 (8 * c')) := by
  unfold Disjoint8
  rw [toNat_sub_ofNat (by omega) (by omega), toNat_sub_ofNat (by omega) (by omega)]
  constructor <;> split <;> omega

/-- **The initial state is related to the source state.** For a well-formed plan that plans
the data roles of the layout, fewer than `2 ^ 11` spans and every span shorter than
`2 ^ 32`, the block-level view of `initState` satisfies `StateRel`: the scalar and length
registers hold the source values, the cells read back at their addresses, distinct cells are
disjoint, and the sink cell is disjoint from every cell. -/
theorem initState_rel (hL : LayoutOK L) (hw : plan.wellFormed = true)
    (hsc : ∀ x ∈ L.scalars, plan.has (.var x) = true)
    (hsp : ∀ t ∈ L.spans, plan.has (.len t) = true ∧ plan.has (.ptr t) = true)
    (hsink : plan.has .sink = true) (hn : L.spans.length < 2 ^ 11)
    (hlen : ∀ t ∈ L.spans, (σ.bufs t).length < spanStride) :
    StateRel L σ (blockView (plan.alloc L) (initState L plan σ)) := by
  have hval : ∀ r, plan.has r = true →
      (blockView (plan.alloc L) (initState L plan σ)).regs (L.name r) = roleVal L σ r := by
    intro r hr
    obtain ⟨k, hk⟩ := RegPlan.has_iff.mp hr
    show initRegs L plan σ (nameOf (plan.alloc L) (L.name r)) = _
    rw [RegPlan.nameOf_alloc hL hw hk, initRegs_regName hw hk]
  have hptr : ∀ t ∈ L.spans,
      (blockView (plan.alloc L) (initState L plan σ)).regs (L.name (.ptr t)) = spanBase L t :=
    fun t ht => hval _ (hsp t ht).2
  have hsinkv : (blockView (plan.alloc L) (initState L plan σ)).regs (L.name .sink) =
      sinkAddr := hval _ hsink
  refine ⟨fun x hx => hval _ (hsc x hx), fun t ht => hval _ (hsp t ht).1,
    fun t ht => by have := hlen t ht; simp only [spanStride] at this; omega,
    fun t ht i hi => ?_, fun t ht t' ht' i j hi hj hne => ?_, fun t ht i hi => ?_⟩
  · rw [hptr t ht]
    exact read64_initMem hn ht hi (hlen t ht)
  · have hi' : i < spanStride := by have := hlen t ht; omega
    have hj' : j < spanStride := by have := hlen t' ht'; omega
    rw [hptr t ht, hptr t' ht', cellAddr_spanBase, cellAddr_spanBase]
    have hc := cellNo_lt hn ht hi'
    have hc' := cellNo_lt hn ht' hj'
    refine disjoint8_ofNat (by omega) (by omega) ?_
    intro e
    apply hne
    simp only [cellNo, spanStride] at e hi' hj'
    have hk : L.spans.idxOf t = L.spans.idxOf t' := by omega
    have htt : t = t' := (List.idxOf_inj ht).mp hk
    subst htt
    have : i = j := by omega
    rw [this]
  · rw [hptr t ht, hsinkv, cellAddr_spanBase]
    have hc := cellNo_lt hn ht (by have := hlen t ht; omega : i < spanStride)
    exact disjoint8_ofNat (by omega) (by decide) (by simp only [cellNo]; omega)

end Init

/-! ## Registered decision procedures -/

/-- A decision procedure for `P : α → Prop`: a fragment program, its layout, register plan
and loop capacities, the source state of an input, and a boolean admissibility test on
inputs; with the checks under which the compiled program runs correctly on the machine
model, and the specification that on an admissible input the program answers `true` exactly
when `P` holds. -/
structure DecisionProc (α : Type) (P : α → Prop) where
  /-- The program. -/
  prog : FProg
  /-- The data placement. -/
  layout : Layout
  /-- The register of each role. -/
  plan : RegPlan
  /-- The number of copies of each `forLen` loop. -/
  cap : String → Nat
  /-- The source state of an input. -/
  toState : α → FState
  /-- The inputs the procedure decides. -/
  admit : α → Bool
  /-- The layout names distinct roles distinctly. -/
  layoutOK : LayoutOK layout
  /-- The program is in the compiled scope with loops. -/
  fitsL : prog.fitsL layout cap = true
  /-- Every literal and loop bound of the program is in range. -/
  litsFitL : prog.litsFitL = true
  /-- The register plan passes `planCheck`. -/
  planOK : planCheck layout plan prog = true
  /-- On an admissible input every span has a length at most its capacity. -/
  admit_capOK : ∀ x, admit x = true → CapOK layout cap (toState x)
  /-- On an admissible input every span is shorter than `2 ^ 32`. -/
  admit_lenLt : ∀ x, admit x = true → ∀ t ∈ layout.spans, ((toState x).bufs t).length < 2 ^ 32
  /-- On an admissible input the program answers `true` exactly when `P` holds. -/
  spec : ∀ x, admit x = true → (prog.run (toState x) = true ↔ P x)

namespace DecisionProc

variable {α : Type} {P : α → Prop} (d : DecisionProc α P)

/-- The allocation of the procedure's register plan. -/
def alloc : GpAlloc := d.plan.alloc d.layout

/-- The compiled code. -/
def code : List (JInstr 64) := compileProgL d.layout d.cap d.prog

/-- The shipped bytes of the compiled code. -/
def bytes : List (BitVec 8) := encodeJBlock6 d.alloc d.code

/-- The physical register of the result temporary. -/
def resReg : String := nameOf d.alloc (tR d.layout 0)

/-- The initial machine state of an input. -/
def init (x : α) : AState := initState d.layout d.plan (d.toState x)

end DecisionProc

/-- **Soundness of the machine run.** For a registered procedure and an admissible input,
an accepting `machineAccepts` run of the procedure's bytes from the input's initial state
proves the proposition. -/
theorem verifiedDecide_sound {α : Type} {P : α → Prop} (d : DecisionProc α P) (x : α)
    (ha : d.admit x = true)
    (h : machineAccepts d.bytes d.code.length (d.init x) d.resReg = true) : P x := by
  obtain ⟨hw, hsc, hsp, hsink, hn, -⟩ := planCheck_spec d.planOK
  have hR := initState_rel (σ := d.toState x) d.layoutOK hw hsc hsp hsink hn
    (d.admit_lenLt x ha)
  obtain ⟨blk, hdec, hiff⟩ := compileProgL_bytes_correct d.layoutOK
    (allocOK_of_planCheck d.layoutOK d.planOK) d.cap d.prog d.fitsL d.litsFitL
    (renInjOn_of_planCheck d.layoutOK d.planOK d.cap) hR (d.admit_capOK x ha)
    (aRelOn_blockView _ _ (initState d.layout d.plan (d.toState x)))
  obtain ⟨blk', hdec', hne⟩ := machineAccepts_eq_true h
  have hb : blk' = blk := by
    simp only [DecisionProc.bytes, DecisionProc.code, DecisionProc.alloc] at hdec'
    rw [hdec] at hdec'
    exact (Option.some.inj hdec').symm
  subst hb
  exact (d.spec x ha).mp (hiff.mp hne)

/-! ## The tactic -/

open Lean Meta Elab Tactic in
/-- Close a goal `head a₁ … aₖ = true` with closed arguments, where `head` of arity `k` is
`machineAccepts` of arity `4` by default: compile and evaluate `head a₁ … aₖ` by
`Lean.Meta.nativeEqTrue`, which on `true` adds the auxiliary axiom
`head a₁ … aₖ = true` and returns it as the proof. Fails with the machine's answer when the
evaluation returns `false`. -/
meta def evalMachineAccepts (g : MVarId) (head : Name := ``machineAccepts) (arity : Nat := 4) :
    TacticM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := ty.eq?
    | throwError "verified_decide: the goal is not an equation{indentExpr ty}"
  unless lhs.isAppOfArity head arity && rhs.isConstOf ``Bool.true do
    throwError "verified_decide: the goal is not `{head} … = true`{indentExpr ty}"
  if lhs.hasFVar || lhs.hasMVar then
    throwError "verified_decide: the machine run has free variables or metavariables{indentExpr lhs}"
  match ← nativeEqTrue `verified_decide lhs with
  | .notTrue => throwError "verified_decide: the machine returned false on{indentExpr lhs}"
  | .success prf => g.assign prf

/-- `machine_accepts` closes `machineAccepts bytes n init res = true` for closed arguments by
evaluating the machine model and asserting the result by an auxiliary axiom. -/
syntax (name := machineAcceptsTac) "machine_accepts" : tactic

open Lean Elab Tactic in
/-- The elaborator of `machine_accepts`. -/
@[tactic machineAcceptsTac] meta def evalMachineAcceptsTac : Tactic := fun _ => do
  evalMachineAccepts (← getMainGoal)
  replaceMainGoal []

/-- `verified_decide d` closes a goal `P x`, for a registered `d : DecisionProc α P` and a
concrete input `x`: it applies `verifiedDecide_sound d x`, decides admissibility of `x` by
`decide`, and closes the machine run by `machine_accepts`. -/
macro "verified_decide " d:term : tactic =>
  `(tactic| (refine verifiedDecide_sound $d _ (by decide) ?_; machine_accepts))

end VerifiedEval

end
