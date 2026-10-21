/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.FragmentCompile

/-!
# Compiling the bounded loops of the fragment by guarded unrolling

An extension of the fragment compiler of
`VerifiedEval.FragmentCompile` to the two loop forms of
`FStmt`, with correctness proved once over all programs against `runBlockA`. The output
stays straight-line `JInstr 64` code.

* `forLit i n body` unrolls to `n` copies of the body, copy `j` preceded by the guarded
  assignment `i := j`; every copy runs under the guard of the loop.
* `forLen i t body` unrolls to `cap t` copies, where `cap t` is a static capacity of span
  `t`. Copy `j` sets the guard register `gThen (k + 1)` to the loop's guard when
  `j < len t` and to `0` otherwise (`cmp` and `cmovb`), and runs the guarded assignment
  `i := j` and the body under it. The runtime length of `t` is read from its length
  register; it may be any value up to `cap t`, zero included.

Nested loops nest the unrolling. Every statement preserves the length of every span
(`FStmt.exec_length`), so the length of `t` at loop entry is the length in the initial
state, and a capacity bound on the initial state (`CapOK`) holds at every loop entry.

## Main definitions

* `compileStmtL`, `compileArmsL`, `compileProgL`: the compiler with loops.
* `FStmt.fitsL`, `FStmt.fitsArmsL`, `FProg.fitsL`: the compiled scope with loops.
* `CapOK`: every span of the layout has a length at most its capacity.
* `FStmt.codeSize`: the length of the compiled code, with loop bounds as factors.

## Main results

* `compileStmtL_eq_of_loopFree`: on a loop-free statement `compileStmtL` is `compileStmt`.
* `compileStmtL_correct`, `compileArmsL_correct`: statement code under a guard holding `1`
  relates the state after the statement, and under a guard holding `0` the state before
  it, for statements with loops.
* `compileProgL_correct`: the result temporary is nonzero after the compiled program
  exactly when `FProg.run` answers `true`.
* `compileStmtL_length`: the code length is `FStmt.codeSize`, in which a `forLit` loop
  contributes `n * (6 + body)` and a `forLen` loop `cap t * (10 + body)` instructions.
* `FStmt.fitsL_eq_fits_of_loopFree`: on a loop-free statement the scope with loops is the
  loop-free scope. The docstring of `FStmt.fitsL` lists which of its conditions are
  obligations on the layout.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem

/-! ## Statements preserve span lengths -/

theorem foldl_length_preserve {α : Type} (F : FState → α → FState)
    (hF : ∀ σ a t, ((F σ a).bufs t).length = (σ.bufs t).length) :
    ∀ (l : List α) (σ : FState) (t : String),
      ((l.foldl F σ).bufs t).length = (σ.bufs t).length
  | [], _, _ => rfl
  | a :: l, σ, t => by
      rw [List.foldl_cons, foldl_length_preserve F hF l _ t, hF]

mutual

/-- A statement leaves the length of every buffer unchanged. -/
theorem FStmt.exec_length (Γ : String → FWidth) :
    ∀ (st : FStmt) (σ : FState) (t : String), ((st.exec Γ σ).bufs t).length = (σ.bufs t).length
  | .skip, _, _ => rfl
  | .seq a b, σ, t => by
      rw [FStmt.exec_seq, FStmt.exec_length Γ b, FStmt.exec_length Γ a]
  | .assign _ _, _, _ => rfl
  | .spanSet s _ _, σ, t => by
      simp only [FStmt.exec, FState.setBuf]
      split <;> simp_all
  | .ite c a b, σ, t => by
      simp only [FStmt.exec]
      split
      · exact FStmt.exec_length Γ b σ t
      · exact FStmt.exec_length Γ a σ t
  | .forLit i n body, σ, t => by
      simp only [FStmt.exec]
      exact foldl_length_preserve (fun st k => body.exec Γ (st.set i (BitVec.ofNat 64 k)))
        (fun σ _ t => (FStmt.exec_length Γ body _ t).trans rfl) _ σ t
  | .forLen i s body, σ, t => by
      simp only [FStmt.exec]
      exact foldl_length_preserve (fun st k => body.exec Γ (st.set i (BitVec.ofNat 64 k)))
        (fun σ _ t => (FStmt.exec_length Γ body _ t).trans rfl) _ σ t
  | .matchTag s arms d, σ, t => by
      simp only [FStmt.exec]
      split
      · rename_i σ' h
        exact FStmt.execArms_length Γ arms _ σ σ' h t
      · exact FStmt.exec_length Γ d σ t

/-- The state after a matching arm has the buffer lengths of the state before it. -/
theorem FStmt.execArms_length (Γ : String → FWidth) :
    ∀ (arms : List (Nat × FStmt)) (tag : Nat) (σ σ' : FState),
      FStmt.execArms Γ tag arms σ = some σ' → ∀ t, (σ'.bufs t).length = (σ.bufs t).length
  | [], _, _, _, h, _ => by simp [FStmt.execArms] at h
  | (k, b) :: rest, tag, σ, σ', h, t => by
      simp only [FStmt.execArms] at h
      split at h
      · cases h; exact FStmt.exec_length Γ b σ t
      · exact FStmt.execArms_length Γ rest tag σ σ' h t

end

/-! ## The compiler with loops -/

/-- The guarded assignment of the literal `j` to the loop variable `i` under guard `g`: the
assignment code of `FStmt.assign i (.lit j)` at width `w64`, whose mask is the identity. -/
def loopVarCode (L : Layout) (g : RegName) (i : String) (j : Nat) : List (JInstr 64) :=
  assignCode L (fun _ => .w64) g i (.lit j)

/-- With guard `g`: the guard register `gThen (k + 1)` gets `g` when `j` is below the length
of span `t`, and `0` otherwise. -/
def lenGuard (L : Layout) (g : RegName) (k : Nat) (t : String) (j : Nat) : List (JInstr 64) :=
  [.mov (tR L 0) (.imm j), .cmp (tR L 0) (.reg (L.name (.len t))),
   .mov (L.name (.gThen (k + 1))) (.imm 0),
   .cmovb (L.name (.gThen (k + 1))) (.reg (L.name g))]

/-- The first `n` copies of a `forLit` loop with body code `c`: copy `j` assigns `j` to the
loop variable under guard `g` and runs `c`. -/
def unrollLit (L : Layout) (g : RegName) (i : String) (c : List (JInstr 64)) :
    Nat → List (JInstr 64)
  | 0 => []
  | n + 1 => unrollLit L g i c n ++ (loopVarCode L g i n ++ c)

/-- The first `m` copies of a `forLen` loop over span `t` with body code `c` at depth
`k + 1`: copy `j` sets `gThen (k + 1)` to `g` when `j` is below the length of `t` and to `0`
otherwise, and runs the loop-variable assignment and `c` under it. -/
def unrollLen (L : Layout) (g : RegName) (k : Nat) (i t : String) (c : List (JInstr 64)) :
    Nat → List (JInstr 64)
  | 0 => []
  | m + 1 => unrollLen L g k i t c m ++
      (lenGuard L g k t m ++ loopVarCode L (.gThen (k + 1)) i m ++ c)

mutual

/-- The code of a statement at nesting depth `k` under guard register `g`, with `cap t` the
number of copies emitted for a `forLen` loop over span `t`. A `forLit` body is compiled at
depth `k` under `g`; a `forLen` body at depth `k + 1` under `gThen (k + 1)`. -/
def compileStmtL (L : Layout) (Γ : String → FWidth) (cap : String → Nat) :
    Nat → RegName → FStmt → List (JInstr 64)
  | _, _, .skip => []
  | k, g, .seq a b => compileStmtL L Γ cap k g a ++ compileStmtL L Γ cap k g b
  | _, g, .assign x e => assignCode L Γ g x e
  | _, g, .spanSet t i v => setCode L Γ g t i v
  | k, g, .ite c a b =>
      compileExpr L Γ 0 c ++ iteGuards L g k ++ compileStmtL L Γ cap (k + 1) (.gThen (k + 1)) a ++
        compileStmtL L Γ cap (k + 1) (.gElse (k + 1)) b
  | k, g, .matchTag t arms dflt =>
      matchPrologue L g k t ++ compileArmsL L Γ cap k arms ++
        compileStmtL L Γ cap (k + 1) (.gElse (k + 1)) dflt
  | k, g, .forLit i n body => unrollLit L g i (compileStmtL L Γ cap k g body) n
  | k, g, .forLen i t body =>
      unrollLen L g k i t (compileStmtL L Γ cap (k + 1) (.gThen (k + 1)) body) (cap t)

/-- The code of the arms of a `matchTag` at depth `k`. -/
def compileArmsL (L : Layout) (Γ : String → FWidth) (cap : String → Nat) (k : Nat) :
    List (Nat × FStmt) → List (JInstr 64)
  | [] => []
  | (tag, b) :: rest =>
      armGuards L k tag ++ compileStmtL L Γ cap (k + 1) (.gThen (k + 1)) b ++
        compileArmsL L Γ cap k rest

end

mutual

/-- The statement is in the compiled scope with loops, for layout `L` and capacities `cap`:
every span it names is a span of `L`, every expression fits, every `matchTag` arm tag is
below `2^64`, and every `forLen` loop runs over a span of `L` whose capacity is at most
`2^64`. The loop variable of a loop need not be a register scalar of `L`.

`FProg.wf` checks names against the program's declarations, not against a layout, so the
membership conditions are obligations on the layout: every scalar read is in `L.scalars`,
and every span or tagged value named is in `L.spans`; `cap t ≤ 2^64` is an obligation on
the capacities. `wf` bounds a shift amount below the operand width only where the shift is
checked against a word type (an assigned or stored value); a shift inside a span index is
typed by `FExpr.infer`, which does not bound the amount. `wf` bounds an arm tag by the
declared tag count, which gives `tag < 2^64` when the count is at most `2^64`. -/
def FStmt.fitsL (L : Layout) (cap : String → Nat) : FStmt → Bool
  | .skip => true
  | .seq a b => a.fitsL L cap && b.fitsL L cap
  | .assign _ e => e.fits L
  | .spanSet t i v => decide (t ∈ L.spans) && i.fits L && v.fits L
  | .ite c a b => c.fits L && a.fitsL L cap && b.fitsL L cap
  | .matchTag t arms dflt =>
      decide (t ∈ L.spans) && FStmt.fitsArmsL L cap arms && dflt.fitsL L cap
  | .forLit _ _ body => body.fitsL L cap
  | .forLen _ t body => decide (t ∈ L.spans) && decide (cap t ≤ 2 ^ 64) && body.fitsL L cap

/-- Every arm is in the compiled scope with loops and has a tag below `2^64`. -/
def FStmt.fitsArmsL (L : Layout) (cap : String → Nat) : List (Nat × FStmt) → Bool
  | [] => true
  | (tag, b) :: rest => decide (tag < 2 ^ 64) && b.fitsL L cap && FStmt.fitsArmsL L cap rest

end

mutual

/-- The statement contains no loop. -/
def FStmt.loopFree : FStmt → Bool
  | .skip | .assign .. | .spanSet .. => true
  | .seq a b => a.loopFree && b.loopFree
  | .ite _ a b => a.loopFree && b.loopFree
  | .matchTag _ arms dflt => FStmt.loopFreeArms arms && dflt.loopFree
  | .forLit .. | .forLen .. => false

/-- No arm contains a loop. -/
def FStmt.loopFreeArms : List (Nat × FStmt) → Bool
  | [] => true
  | (_, b) :: rest => b.loopFree && FStmt.loopFreeArms rest

end

/-- The compiled program with loops: set the depth-0 guard to `1`, run the body, and leave
the value of the result expression in temporary 0. -/
def compileProgL (L : Layout) (cap : String → Nat) (p : FProg) : List (JInstr 64) :=
  .mov (L.name (.gThen 0)) (.imm 1) :: compileStmtL L p.widths cap 0 (.gThen 0) p.body ++
    compileExpr L p.widths 0 p.result

/-- The program is in the compiled scope with loops. -/
def FProg.fitsL (L : Layout) (cap : String → Nat) (p : FProg) : Bool :=
  p.body.fitsL L cap && p.result.fits L

/-- Every span of the layout has a length at most its capacity. -/
def CapOK (L : Layout) (cap : String → Nat) (σ : FState) : Prop :=
  ∀ t ∈ L.spans, (σ.bufs t).length ≤ cap t

theorem CapOK.of_length {L : Layout} {cap : String → Nat} {σ σ' : FState} (h : CapOK L cap σ)
    (hl : ∀ t, (σ'.bufs t).length = (σ.bufs t).length) : CapOK L cap σ' :=
  fun t ht => (hl t).symm ▸ h t ht

theorem CapOK.exec {L : Layout} {cap : String → Nat} {σ : FState} (h : CapOK L cap σ)
    (Γ : String → FWidth) (st : FStmt) (b : Bool) :
    CapOK L cap (if b then st.exec Γ σ else σ) := by
  cases b
  · exact h
  · exact h.of_length (FStmt.exec_length Γ st σ)

/-! ## Correctness of the loop code -/

theorem and_w64_mask (v : BitVec 64) : v &&& FWidth.w64.mask = v := by
  have : FWidth.w64.mask = BitVec.allOnes 64 := by decide
  rw [this, BitVec.and_allOnes]

/-- **Guarded loop-variable assignment.** Under a guard holding `1` the code relates the
state with `i` set to `j`, and under a guard holding `0` the state before it. -/
theorem loopVarCode_correct {L : Layout} (hL : LayoutOK L) {σ : FState} {s : AState} {k : Nat}
    {g : RegName} (hg : g.guardAt k = true) (b : Bool)
    (hgv : s.regs (L.name g) = if b then 1 else 0) (i : String) (j : Nat)
    (hR : StateRel L σ s) :
    StateRel L (if b then σ.set i (BitVec.ofNat 64 j) else σ) (runBlockA s (loopVarCode L g i j)) ∧
      StmtFrame L k s (runBlockA s (loopVarCode L g i j)) := by
  have h := assignCode_correct hL (fun _ => .w64) hg b hgv (x := i) (e := .lit j) rfl hR
  unfold loopVarCode
  simpa only [FStmt.exec, FExpr.eval, and_w64_mask] using h

theorem lenGuard_spec {L : Layout} (hL : LayoutOK L) {k : Nat} {g : RegName}
    (hg : g.guardAt k = true) (b : Bool) (s : AState)
    (hgv : s.regs (L.name g) = if b then 1 else 0) (t : String) {j n : Nat} (hj : j < 2 ^ 64)
    (hn : n < 2 ^ 64) (hlen : s.regs (L.name (.len t)) = BitVec.ofNat 64 n) :
    (runBlockA s (lenGuard L g k t j)).regs (L.name (.gThen (k + 1))) =
        (if (b && decide (j < n)) = true then 1 else 0) ∧
      (∀ r, (∀ j, r ≠ .tmp j) → r ≠ .gThen (k + 1) →
        (runBlockA s (lenGuard L g k t j)).regs (L.name r) = s.regs (L.name r)) ∧
      (runBlockA s (lenGuard L g k t j)).mem = s.mem := by
  have hgt : ∀ j, g ≠ .tmp j := RegName.not_tmp_of_guardAt hg
  have hg1 : g ≠ .gThen (k + 1) := by rintro rfl; simp [RegName.guardAt] at hg; omega
  have hg0 := hgt 0
  simp only [lenGuard, runBlockA_cons, runBlockA_nil, evalA_mov, evalA_cmp, evalA_cmovb]
  refine ⟨?_, ?_, by first | rfl | trivial⟩
  · simp only [tR, upd, opv, hL.eq_iff, cmpFlags_cf]
    have hc : decide (BitVec.ofNat 64 j < BitVec.ofNat 64 n) = decide (j < n) := by
      apply decide_eq_decide.mpr
      rw [lt_ofNat_iff _ _ hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]
    simp only [reduceCtorEq, if_false, if_true, hlen, hc, hg1, hgv]
    by_cases h : j < n <;> cases b <;> simp [h, hg0]
  · intro r hr h1
    simp [tR, upd, hL.eq_iff, hr, h1]

/-- Statement code `c` at depth `k` under guard `g` simulates `st`: under a guard holding
`1` it relates the state after `st`, under a guard holding `0` the state before it, and it
changes no named register that code at depth `k` does not write. -/
def GuardedSpec (L : Layout) (cap : String → Nat) (Γ : String → FWidth) (k : Nat) (g : RegName)
    (st : FStmt) (c : List (JInstr 64)) : Prop :=
  ∀ (σ : FState) (s : AState) (b : Bool), s.regs (L.name g) = (if b then 1 else 0) →
    StateRel L σ s → CapOK L cap σ →
    StateRel L (if b then st.exec Γ σ else σ) (runBlockA s c) ∧ StmtFrame L k s (runBlockA s c)

/-- **Unrolled `forLit`.** `n` copies of simulating body code simulate `forLit i n body`. -/
theorem unrollLit_correct {L : Layout} (hL : LayoutOK L) (Γ : String → FWidth)
    (cap : String → Nat) {k : Nat} {g : RegName} (hg : g.guardAt k = true) (i : String)
    (body : FStmt) (c : List (JInstr 64)) (hc : GuardedSpec L cap Γ k g body c) :
    ∀ n, GuardedSpec L cap Γ k g (.forLit i n body) (unrollLit L g i c n)
  | 0 => fun σ s b _ hR _ => by
      simp only [unrollLit, runBlockA_nil, FStmt.exec_forLit_zero, ite_self]
      exact ⟨hR, fun _ _ => rfl⟩
  | n + 1 => fun σ s b hgv hR hC => by
      simp only [unrollLit, runBlockA_append]
      obtain ⟨r1, f1⟩ := unrollLit_correct hL Γ cap hg i body c hc n σ s b hgv hR hC
      have hgv1 := (f1 g (RegName.written_of_guardAt hg)).trans hgv
      obtain ⟨r2, f2⟩ := loopVarCode_correct hL hg b hgv1 i n r1
      have hgv2 := (f2 g (RegName.written_of_guardAt hg)).trans hgv1
      have hC1 := hC.exec Γ (.forLit i n body) b
      obtain ⟨r3, f3⟩ := hc _ _ b hgv2 r2 (by cases b <;> exact hC1)
      refine ⟨?_, f1.trans (f2.trans f3)⟩
      cases b <;> simpa [FStmt.exec_forLit_succ] using r3

/-- **Unrolled `forLen`.** For `m ≤ 2^64`, the first `m` copies of the `forLen` code with
simulating body code at depth `k + 1` under `gThen (k + 1)` run the body for the indices
below both `m` and the length of span `t`. -/
theorem unrollLen_correct {L : Layout} (hL : LayoutOK L) (Γ : String → FWidth)
    (cap : String → Nat) {k : Nat} {g : RegName} (hg : g.guardAt k = true) (i t : String)
    (ht : t ∈ L.spans) (body : FStmt) (c : List (JInstr 64))
    (hc : GuardedSpec L cap Γ (k + 1) (.gThen (k + 1)) body c) :
    ∀ m, m ≤ 2 ^ 64 → ∀ (σ : FState) (s : AState) (b : Bool),
      s.regs (L.name g) = (if b then 1 else 0) → StateRel L σ s → CapOK L cap σ →
      StateRel L (if b then (List.range (min m (σ.bufs t).length)).foldl
          (fun st j => body.exec Γ (st.set i (BitVec.ofNat 64 j))) σ else σ)
          (runBlockA s (unrollLen L g k i t c m)) ∧
        StmtFrame L k s (runBlockA s (unrollLen L g k i t c m))
  | 0, _, σ, s, b, _, hR, _ => by
      simp only [unrollLen, runBlockA_nil, Nat.zero_min, List.range_zero, List.foldl_nil,
        ite_self]
      exact ⟨hR, fun _ _ => rfl⟩
  | m + 1, hm, σ, s, b, hgv, hR, hC => by
      simp only [unrollLen, runBlockA_append]
      obtain ⟨r1, f1⟩ := unrollLen_correct hL Γ cap hg i t ht body c hc m (by omega) σ s b hgv hR hC
      have hgv1 := (f1 g (RegName.written_of_guardAt hg)).trans hgv
      have hlen1 := (f1 (.len t) rfl).trans (hR.len t ht)
      obtain ⟨g1, g3, g4⟩ := lenGuard_spec hL hg b _ hgv1 t (j := m) (by omega) (hR.lenLt t ht)
        hlen1
      have hC1 : CapOK L cap (if b then (List.range (min m (σ.bufs t).length)).foldl
          (fun (st : FState) (j : Nat) => body.exec Γ (st.set i (BitVec.ofNat 64 j))) σ
          else σ) := by
        cases b
        · exact hC
        · exact hC.of_length (foldl_length_preserve
            (fun (st : FState) (j : Nat) => body.exec Γ (st.set i (BitVec.ofNat 64 j)))
            (fun σ _ u => FStmt.exec_length Γ body _ u) _ σ)
      generalize runBlockA s (unrollLen L g k i t c m) = s1 at r1 f1 g1 g3 g4
      generalize runBlockA s1 (lenGuard L g k t m) = s2 at g1 g3 g4
      have hR2 := r1.frame (fun n hn => by
        obtain ⟨h1, h2, -, -⟩ := RegName.ne_of_scratch hn
        exact g3 n h1 (h2 _)) g4
      have f2 : StmtFrame L k s1 s2 := fun n hn => by
        obtain ⟨h1, h2, -, -⟩ := RegName.ne_of_written hn
        exact g3 n h1 h2
      obtain ⟨r3, f3⟩ := loopVarCode_correct hL (k := k + 1) (by simp [RegName.guardAt]) _ g1 i m
        hR2
      have hgv3 := (f3 (.gThen (k + 1)) (by simp [RegName.written])).trans g1
      obtain ⟨r4, f4⟩ := hc _ _ _ hgv3 r3 (by
        cases (b && decide (m < (σ.bufs t).length)) <;> exact hC1)
      refine ⟨?_, f1.trans (f2.trans (f3.succ.trans f4.succ))⟩
      cases b
      · simpa using r4
      · by_cases hlt : m < (σ.bufs t).length
        · have e1 : min m (σ.bufs t).length = m := Nat.min_eq_left hlt.le
          have e2 : min (m + 1) (σ.bufs t).length = m + 1 := Nat.min_eq_left hlt
          simp only [e1, if_true] at r4
          simp only [e2, if_true, List.range_succ, List.foldl_append, List.foldl_cons,
            List.foldl_nil]
          simpa [hlt] using r4
        · have e1 : min m (σ.bufs t).length = (σ.bufs t).length := by omega
          have e2 : min (m + 1) (σ.bufs t).length = (σ.bufs t).length := by omega
          simp only [e1, if_true] at r4
          simp only [e2, if_true]
          simpa [hlt] using r4

/-! ## Correctness of the statement compiler with loops -/

mutual

/-- **Statement compiler correctness with loops.** For a statement in the scope with loops,
compiled at depth `k` under a guard register of depth at most `k` holding `1` or `0` as `b`
is true or false, from a state whose spans have lengths at most their capacities, the code
relates the state after the statement when `b` holds and the state before it otherwise,
and changes no named register outside the temporaries, the scalar registers and the guard
registers of depths above `k`. -/
theorem compileStmtL_correct {L : Layout} (hL : LayoutOK L) (Γ : String → FWidth)
    (cap : String → Nat) :
    ∀ (st : FStmt) (k : Nat) (g : RegName) (σ : FState) (s : AState) (b : Bool),
      st.fitsL L cap = true → g.guardAt k = true → s.regs (L.name g) = (if b then 1 else 0) →
      StateRel L σ s → CapOK L cap σ →
      StateRel L (if b then st.exec Γ σ else σ) (runBlockA s (compileStmtL L Γ cap k g st)) ∧
        StmtFrame L k s (runBlockA s (compileStmtL L Γ cap k g st))
  | .skip, _, _, σ, s, b, _, _, _, hR, _ => by
      simp only [compileStmtL, runBlockA_nil, FStmt.exec, ite_self]
      exact ⟨hR, fun _ _ => rfl⟩
  | .seq a c, k, g, σ, s, b, hf, hg, hgv, hR, hC => by
      simp only [FStmt.fitsL, Bool.and_eq_true] at hf
      simp only [compileStmtL, runBlockA_append]
      obtain ⟨r1, f1⟩ := compileStmtL_correct hL Γ cap a k g σ s b hf.1 hg hgv hR hC
      have hgv1 := (f1 g (RegName.written_of_guardAt hg)).trans hgv
      obtain ⟨r2, f2⟩ := compileStmtL_correct hL Γ cap c k g _ _ b hf.2 hg hgv1 r1
        (hC.exec Γ a b)
      refine ⟨?_, f1.trans f2⟩
      cases b <;> simpa [FStmt.exec] using r2
  | .assign x e, k, g, σ, s, b, hf, hg, hgv, hR, _ => by
      simp only [FStmt.fitsL] at hf
      simp only [compileStmtL]
      exact assignCode_correct hL Γ hg b hgv hf hR
  | .spanSet t i v, k, g, σ, s, b, hf, hg, hgv, hR, _ => by
      simp only [FStmt.fitsL, Bool.and_eq_true, decide_eq_true_eq] at hf
      simp only [compileStmtL]
      exact setCode_correct hL Γ hg b hgv hf.1.1 hf.1.2 hf.2 hR
  | .ite c a e, k, g, σ, s, b, hf, hg, hgv, hR, hC => by
      simp only [FStmt.fitsL, Bool.and_eq_true] at hf
      simp only [compileStmtL, runBlockA_append]
      obtain ⟨c1, c2⟩ := compileExpr_correct hL Γ c 0 s hf.1.1 hR
      have hgv1 := (c2.1 g (fun j _ => RegName.not_tmp_of_guardAt hg j)).trans hgv
      obtain ⟨g1, g2, g3, g4⟩ := iteGuards_spec hL hg b _ hgv1
      rw [c1] at g1 g2
      have hR1 := c2.stateRel hR
      have f1 := c2.stmtFrame (k := k)
      generalize runBlockA s (compileExpr L Γ 0 c) = s1 at g1 g2 g3 g4 hR1 f1
      generalize runBlockA s1 (iteGuards L g k) = s2 at g1 g2 g3 g4
      have hR2 : StateRel L σ s2 := hR1.frame (fun n hn => by
        obtain ⟨h1, h2, h3, -⟩ := RegName.ne_of_scratch hn
        exact g3 n h1 (h2 _) (h3 _)) g4
      have f2 : StmtFrame L k s s2 := f1.trans (fun n hn => by
        obtain ⟨h1, h2, h3, -⟩ := RegName.ne_of_written hn
        exact g3 n h1 h2 h3)
      obtain ⟨r3, f3⟩ := compileStmtL_correct hL Γ cap a (k + 1) (.gThen (k + 1)) σ s2 _
        hf.1.2 (by simp [RegName.guardAt]) g1 hR2 hC
      have ge3 := (f3 (.gElse (k + 1)) (by simp [RegName.written])).trans g2
      obtain ⟨r4, f4⟩ := compileStmtL_correct hL Γ cap e (k + 1) (.gElse (k + 1)) _ _ _ hf.2
        (by simp [RegName.guardAt]) ge3 r3 (hC.exec Γ a _)
      refine ⟨?_, f2.trans (f3.succ.trans f4.succ)⟩
      cases b
      · simpa using r4
      · by_cases hc : c.eval Γ σ = 0
        · have e1 : (true && (c.eval Γ σ != 0)) = false := by simp [hc]
          have e2 : (true && (c.eval Γ σ == 0)) = true := by simp [hc]
          rw [e1, e2] at r4
          simp only [FStmt.exec, if_pos hc, if_true]
          simpa using r4
        · have e1 : (true && (c.eval Γ σ != 0)) = true := by simp; exact hc
          have e2 : (true && (c.eval Γ σ == 0)) = false := by simp; exact hc
          rw [e1, e2] at r4
          simp only [FStmt.exec, if_neg hc, if_true]
          simpa using r4
  | .matchTag t arms dflt, k, g, σ, s, b, hf, hg, hgv, hR, hC => by
      simp only [FStmt.fitsL, Bool.and_eq_true, decide_eq_true_eq] at hf
      simp only [compileStmtL, runBlockA_append]
      obtain ⟨p1, p2, p3, p4⟩ := matchPrologue_spec hL hg hR hf.1.1
      rw [hgv] at p2
      generalize runBlockA s (matchPrologue L g k t) = s1 at p1 p2 p3 p4
      have hR1 : StateRel L σ s1 := hR.frame (fun n hn => by
        obtain ⟨h1, -, h3, h4⟩ := RegName.ne_of_scratch hn
        exact p3 n h1 (h4 _) (h3 _)) p4
      have f1 : StmtFrame L k s s1 := fun n hn => by
        obtain ⟨h1, -, h3, h4⟩ := RegName.ne_of_written hn
        exact p3 n h1 h4 h3
      obtain ⟨a1, a2, -, a4⟩ :=
        compileArmsL_correct hL Γ cap arms k σ s1 b _ hf.1.2 p1 p2 hR1 hC
      have hCa : CapOK L cap
          (if b then (FStmt.execArms Γ ((σ.bufs t).getD 0 0).toNat arms σ).getD σ else σ) := by
        cases b
        · exact hC
        · rcases hx : FStmt.execArms Γ ((σ.bufs t).getD 0 0).toNat arms σ with _ | σ'
          · exact hC
          · exact hC.of_length (FStmt.execArms_length Γ arms _ σ σ' hx)
      obtain ⟨d1, d2⟩ := compileStmtL_correct hL Γ cap dflt (k + 1) (.gElse (k + 1)) _ _ _ hf.2
        (by simp [RegName.guardAt]) a2 a1 hCa
      refine ⟨?_, f1.trans (a4.trans d2.succ)⟩
      cases b
      · simpa using d1
      · simp only [FStmt.exec, if_true, Bool.true_and] at d1 ⊢
        rcases hx : FStmt.execArms Γ ((σ.bufs t).getD 0 0).toNat arms σ with _ | σ' <;>
          simp only [hx, Option.isNone_none, Option.isNone_some, Option.getD_none,
            Option.getD_some, if_true, if_false, Bool.false_eq_true] at d1 ⊢ <;> exact d1
  | .forLit i n body, k, g, σ, s, b, hf, hg, hgv, hR, hC => by
      simp only [FStmt.fitsL] at hf
      simp only [compileStmtL]
      exact unrollLit_correct hL Γ cap hg i body _
        (fun σ s b hgv hR hC => compileStmtL_correct hL Γ cap body k g σ s b hf hg hgv hR hC)
        n σ s b hgv hR hC
  | .forLen i t body, k, g, σ, s, b, hf, hg, hgv, hR, hC => by
      simp only [FStmt.fitsL, Bool.and_eq_true, decide_eq_true_eq] at hf
      simp only [compileStmtL]
      obtain ⟨r, f⟩ := unrollLen_correct hL Γ cap hg i t hf.1.1 body _
        (fun σ s b hgv hR hC => compileStmtL_correct hL Γ cap body (k + 1) (.gThen (k + 1))
          σ s b hf.2 (by simp [RegName.guardAt]) hgv hR hC)
        (cap t) hf.1.2 σ s b hgv hR hC
      refine ⟨?_, f⟩
      rw [Nat.min_eq_right (hC t hf.1.1)] at r
      simpa only [FStmt.exec] using r

/-- **Arm compiler correctness with loops.** With the tag word `w` in `gTag (k + 1)` and the
not-yet-matched flag `rem` in `gElse (k + 1)`, the arms' code relates the state after the
first arm whose tag is `w.toNat` when `rem` holds and such an arm exists, and the state
before it otherwise; the flag register ends holding whether `rem` held and no arm
matched. -/
theorem compileArmsL_correct {L : Layout} (hL : LayoutOK L) (Γ : String → FWidth)
    (cap : String → Nat) :
    ∀ (arms : List (Nat × FStmt)) (k : Nat) (σ : FState) (s : AState) (rem : Bool)
      (w : BitVec 64), FStmt.fitsArmsL L cap arms = true →
      s.regs (L.name (.gTag (k + 1))) = w →
      s.regs (L.name (.gElse (k + 1))) = (if rem then 1 else 0) → StateRel L σ s →
      CapOK L cap σ →
      StateRel L (if rem then (FStmt.execArms Γ w.toNat arms σ).getD σ else σ)
          (runBlockA s (compileArmsL L Γ cap k arms)) ∧
        (runBlockA s (compileArmsL L Γ cap k arms)).regs (L.name (.gElse (k + 1))) =
          (if (rem && (FStmt.execArms Γ w.toNat arms σ).isNone) = true then 1 else 0) ∧
        (runBlockA s (compileArmsL L Γ cap k arms)).regs (L.name (.gTag (k + 1))) = w ∧
        StmtFrame L k s (runBlockA s (compileArmsL L Γ cap k arms))
  | [], _, σ, s, rem, _, _, hw, hr, hR, _ => by
      simp only [compileArmsL, runBlockA_nil, FStmt.execArms, Option.getD_none, ite_self,
        Option.isNone_none, Bool.and_true]
      exact ⟨hR, hr, hw, fun _ _ => rfl⟩
  | (tag, body) :: rest, k, σ, s, rem, w, hf, hw, hr, hR, hC => by
      simp only [FStmt.fitsArmsL, Bool.and_eq_true, decide_eq_true_eq] at hf
      simp only [compileArmsL, runBlockA_append]
      obtain ⟨g1, g2, g3, g4⟩ := armGuards_spec hL k tag rem s hr
      have hdec : decide (w = BitVec.ofNat 64 tag) = decide (tag = w.toNat) :=
        decide_eq_decide.mpr (eq_ofNat_iff w tag hf.1.1)
      rw [hw, hdec] at g1 g2
      set s1 := runBlockA s (armGuards L k tag) with hs1
      have hw1 : s1.regs (L.name (.gTag (k + 1))) = w :=
        (g3 _ (fun j e => by cases e) (by simp) (by simp)).trans hw
      have hR1 : StateRel L σ s1 := hR.frame (fun n hn => by
        obtain ⟨h1, h2, h3, -⟩ := RegName.ne_of_scratch hn
        exact g3 n h1 (h2 _) (h3 _)) g4
      have f1 : StmtFrame L k s s1 := fun n hn => by
        obtain ⟨h1, h2, h3, -⟩ := RegName.ne_of_written hn
        exact g3 n h1 h2 h3
      obtain ⟨r2, f2⟩ := compileStmtL_correct hL Γ cap body (k + 1) (.gThen (k + 1)) σ s1 _
        hf.1.2 (by simp [RegName.guardAt]) g1 hR1 hC
      have ge2 := (f2 (.gElse (k + 1)) (by simp [RegName.written])).trans g2
      have gt2 := (f2 (.gTag (k + 1)) (by simp [RegName.written])).trans hw1
      obtain ⟨a1, a2, a3, a4⟩ := compileArmsL_correct hL Γ cap rest k _ _ _ w hf.2 gt2 ge2 r2
        (hC.exec Γ body _)
      refine ⟨?_, ?_, a3, f1.trans (f2.succ.trans a4)⟩
      · generalize runBlockA (runBlockA s1 (compileStmtL L Γ cap (k + 1) (.gThen (k + 1)) body))
          (compileArmsL L Γ cap k rest) = sF at a1 ⊢
        cases rem <;> by_cases hk : tag = w.toNat <;>
          simp [FStmt.execArms, hk] at a1 ⊢ <;> exact a1
      · rw [a2]
        cases rem <;> by_cases hk : tag = w.toNat <;> simp [FStmt.execArms, hk]

end

/-- **Program compiler correctness with loops.** For a program in the scope with loops and
a machine state related to a source state whose spans have lengths at most their
capacities, temporary 0 is nonzero after the compiled program exactly when the program
answers `true`. -/
theorem compileProgL_correct {L : Layout} (hL : LayoutOK L) (cap : String → Nat) (p : FProg)
    (hf : p.fitsL L cap = true) {σ : FState} {s : AState} (hR : StateRel L σ s)
    (hC : CapOK L cap σ) :
    (runBlockA s (compileProgL L cap p)).regs (tR L 0) ≠ 0 ↔ p.run σ = true := by
  simp only [FProg.fitsL, Bool.and_eq_true] at hf
  simp only [compileProgL, List.cons_append, runBlockA_cons, runBlockA_append]
  have hR0 : StateRel L σ (evalInstrA s (.mov (L.name (.gThen 0)) (.imm 1))) := by
    refine hR.frame (fun n hn => ?_) (by rw [evalA_mov])
    obtain ⟨-, h2, -, -⟩ := RegName.ne_of_scratch hn
    rw [evalA_mov]
    simp [upd, hL.eq_iff, h2 0]
  have hg0 : (evalInstrA s (.mov (L.name (.gThen 0)) (.imm 1))).regs (L.name (.gThen 0)) =
      if true = true then 1 else 0 := by
    rw [evalA_mov]; simp [upd, opv]
  obtain ⟨r1, -⟩ := compileStmtL_correct hL p.widths cap p.body 0 (.gThen 0) σ _ true hf.1
    (by simp [RegName.guardAt]) hg0 hR0 hC
  simp only [if_true] at r1
  obtain ⟨e1, -⟩ := compileExpr_correct hL p.widths p.result 0 _ hf.2 r1
  rw [e1]
  simp [FProg.run]

/-! ## Agreement with the loop-free compiler -/

mutual

/-- On a loop-free statement `compileStmtL` is `compileStmt`. -/
theorem compileStmtL_eq_of_loopFree (L : Layout) (Γ : String → FWidth) (cap : String → Nat) :
    ∀ (st : FStmt) (k : Nat) (g : RegName), st.loopFree = true →
      compileStmtL L Γ cap k g st = compileStmt L Γ k g st
  | .skip, _, _, _ => by simp only [compileStmtL, compileStmt]
  | .seq a b, k, g, h => by
      simp only [FStmt.loopFree, Bool.and_eq_true] at h
      simp only [compileStmtL, compileStmt, compileStmtL_eq_of_loopFree L Γ cap a k g h.1,
        compileStmtL_eq_of_loopFree L Γ cap b k g h.2]
  | .assign .., _, _, _ => by simp only [compileStmtL, compileStmt]
  | .spanSet .., _, _, _ => by simp only [compileStmtL, compileStmt]
  | .ite c a b, k, g, h => by
      simp only [FStmt.loopFree, Bool.and_eq_true] at h
      simp only [compileStmtL, compileStmt,
        compileStmtL_eq_of_loopFree L Γ cap a _ _ h.1, compileStmtL_eq_of_loopFree L Γ cap b _ _ h.2]
  | .matchTag t arms d, k, g, h => by
      simp only [FStmt.loopFree, Bool.and_eq_true] at h
      simp only [compileStmtL, compileStmt, compileArmsL_eq_of_loopFree L Γ cap k arms h.1,
        compileStmtL_eq_of_loopFree L Γ cap d _ _ h.2]
  | .forLit .., _, _, h => by simp [FStmt.loopFree] at h
  | .forLen .., _, _, h => by simp [FStmt.loopFree] at h

/-- On loop-free arms `compileArmsL` is `compileArms`. -/
theorem compileArmsL_eq_of_loopFree (L : Layout) (Γ : String → FWidth) (cap : String → Nat)
    (k : Nat) : ∀ (arms : List (Nat × FStmt)), FStmt.loopFreeArms arms = true →
      compileArmsL L Γ cap k arms = compileArms L Γ k arms
  | [], _ => by simp only [compileArmsL, compileArms]
  | (tag, b) :: rest, h => by
      simp only [FStmt.loopFreeArms, Bool.and_eq_true] at h
      simp only [compileArmsL, compileArms, compileStmtL_eq_of_loopFree L Γ cap b _ _ h.1,
        compileArmsL_eq_of_loopFree L Γ cap k rest h.2]

end

mutual

/-- On a loop-free statement the scope with loops is the loop-free scope. -/
theorem FStmt.fitsL_eq_fits_of_loopFree (L : Layout) (cap : String → Nat) :
    ∀ (st : FStmt), st.loopFree = true → st.fitsL L cap = st.fits L
  | .skip, _ => rfl
  | .seq a b, h => by
      simp only [FStmt.loopFree, Bool.and_eq_true] at h
      simp only [FStmt.fitsL, FStmt.fits, FStmt.fitsL_eq_fits_of_loopFree L cap a h.1,
        FStmt.fitsL_eq_fits_of_loopFree L cap b h.2]
  | .assign .., _ => rfl
  | .spanSet .., _ => rfl
  | .ite c a b, h => by
      simp only [FStmt.loopFree, Bool.and_eq_true] at h
      simp only [FStmt.fitsL, FStmt.fits, FStmt.fitsL_eq_fits_of_loopFree L cap a h.1,
        FStmt.fitsL_eq_fits_of_loopFree L cap b h.2]
  | .matchTag t arms d, h => by
      simp only [FStmt.loopFree, Bool.and_eq_true] at h
      simp only [FStmt.fitsL, FStmt.fits, FStmt.fitsArmsL_eq_fitsArms_of_loopFree L cap arms h.1,
        FStmt.fitsL_eq_fits_of_loopFree L cap d h.2]
  | .forLit .., h => by simp [FStmt.loopFree] at h
  | .forLen .., h => by simp [FStmt.loopFree] at h

/-- On loop-free arms the scope with loops is the loop-free scope. -/
theorem FStmt.fitsArmsL_eq_fitsArms_of_loopFree (L : Layout) (cap : String → Nat) :
    ∀ (arms : List (Nat × FStmt)), FStmt.loopFreeArms arms = true →
      FStmt.fitsArmsL L cap arms = FStmt.fitsArms L arms
  | [], _ => rfl
  | (tag, b) :: rest, h => by
      simp only [FStmt.loopFreeArms, Bool.and_eq_true] at h
      simp only [FStmt.fitsArmsL, FStmt.fitsArms, FStmt.fitsL_eq_fits_of_loopFree L cap b h.1,
        FStmt.fitsArmsL_eq_fitsArms_of_loopFree L cap rest h.2]

end

/-! ## Code size -/

mutual

/-- The number of instructions `compileStmtL` emits for a statement. A `forLit i n body`
loop costs `n * (6 + body)` and a `forLen i t body` loop `cap t * (10 + body)`, so the
code size of nested loops is the product of their trip bounds times the body size. -/
def FStmt.codeSize (L : Layout) (Γ : String → FWidth) (cap : String → Nat) : FStmt → Nat
  | .skip => 0
  | .seq a b => a.codeSize L Γ cap + b.codeSize L Γ cap
  | .assign _ e => (compileExpr L Γ 0 e).length + 5
  | .spanSet _ i v => (compileExpr L Γ 0 v).length + (compileExpr L Γ 1 i).length + 12
  | .ite c a b => (compileExpr L Γ 0 c).length + 6 + a.codeSize L Γ cap + b.codeSize L Γ cap
  | .matchTag _ arms dflt => 11 + FStmt.codeSizeArms L Γ cap arms + dflt.codeSize L Γ cap
  | .forLit _ n body => n * (6 + body.codeSize L Γ cap)
  | .forLen _ t body => cap t * (10 + body.codeSize L Γ cap)

/-- The number of instructions `compileArmsL` emits for the arms of a `matchTag`. -/
def FStmt.codeSizeArms (L : Layout) (Γ : String → FWidth) (cap : String → Nat) :
    List (Nat × FStmt) → Nat
  | [] => 0
  | (_, b) :: rest => 6 + b.codeSize L Γ cap + FStmt.codeSizeArms L Γ cap rest

end

theorem unrollLit_length (L : Layout) (g : RegName) (i : String) (c : List (JInstr 64)) :
    ∀ n, (unrollLit L g i c n).length = n * (6 + c.length)
  | 0 => by simp [unrollLit]
  | n + 1 => by
      simp only [unrollLit, List.length_append, unrollLit_length L g i c n]
      simp [loopVarCode, assignCode, compileExpr, maskCode]
      exact (Nat.succ_mul _ _).symm

theorem unrollLen_length (L : Layout) (g : RegName) (k : Nat) (i t : String)
    (c : List (JInstr 64)) : ∀ m, (unrollLen L g k i t c m).length = m * (10 + c.length)
  | 0 => by simp [unrollLen]
  | m + 1 => by
      simp only [unrollLen, List.length_append, unrollLen_length L g k i t c m]
      simp [lenGuard, loopVarCode, assignCode, compileExpr, maskCode]
      exact (Nat.succ_mul _ _).symm

mutual

/-- **Code size.** The compiled code of a statement has `FStmt.codeSize` instructions. -/
theorem compileStmtL_length (L : Layout) (Γ : String → FWidth) (cap : String → Nat) :
    ∀ (st : FStmt) (k : Nat) (g : RegName),
      (compileStmtL L Γ cap k g st).length = st.codeSize L Γ cap
  | .skip, _, _ => rfl
  | .seq a b, k, g => by
      simp only [compileStmtL, FStmt.codeSize, List.length_append,
        compileStmtL_length L Γ cap a, compileStmtL_length L Γ cap b]
  | .assign x e, _, g => by
      simp [compileStmtL, FStmt.codeSize, assignCode, maskCode]
  | .spanSet t i v, _, g => by
      simp [compileStmtL, FStmt.codeSize, setCode, maskCode, selCode]
      omega
  | .ite c a b, k, g => by
      simp only [compileStmtL, FStmt.codeSize, List.length_append,
        compileStmtL_length L Γ cap a, compileStmtL_length L Γ cap b]
      simp [iteGuards]
  | .matchTag t arms d, k, g => by
      simp only [compileStmtL, FStmt.codeSize, List.length_append,
        compileArmsL_length L Γ cap k arms, compileStmtL_length L Γ cap d]
      simp [matchPrologue, getCode, selCode]
  | .forLit i n body, k, g => by
      simp only [compileStmtL, FStmt.codeSize, unrollLit_length, compileStmtL_length L Γ cap body]
  | .forLen i t body, k, g => by
      simp only [compileStmtL, FStmt.codeSize, unrollLen_length, compileStmtL_length L Γ cap body]

/-- The compiled code of `matchTag` arms has `FStmt.codeSizeArms` instructions. -/
theorem compileArmsL_length (L : Layout) (Γ : String → FWidth) (cap : String → Nat) (k : Nat) :
    ∀ (arms : List (Nat × FStmt)),
      (compileArmsL L Γ cap k arms).length = FStmt.codeSizeArms L Γ cap arms
  | [] => rfl
  | (tag, b) :: rest => by
      simp only [compileArmsL, FStmt.codeSizeArms, List.length_append,
        compileStmtL_length L Γ cap b, compileArmsL_length L Γ cap k rest]
      simp [armGuards]

end

end VerifiedEval

end
