/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.Fragment
public import VerifiedEval.Arena
public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem

/-!
# Compiling the loop-free fragment to `JInstr 64`

A compiler from the loop-free part of the decision-procedure fragment
(`VerifiedEval.Fragment`) to straight-line `JInstr 64`
code, with its correctness proved once over all programs against the address-memory
machine `runBlockA` of `CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem`.

The emitted code uses `mov`, `add`, `sub`, `imul`, `and`, `or`, `xor`, `shl` and `shr` by
an immediate, `cmp`, `cmove`, `cmovne`, `cmovb` with a register source, and the indexed
`loadMemIdx`/`storeMemIdx` at scale 8. It contains no branch: a comparison is a `cmp`
followed by a conditional move of `0` or `1`, and `ite` and `matchTag` run every arm under
a guard register. A span read or write compares the index with the span's length and, when
the index is out of range, reads or writes the sink cell instead; a read then yields `0`,
as `FExpr.eval` specifies, and a write leaves the span unchanged, as `List.set` does.

## Layout and relation

A `Layout` names a register for each role (`RegName`): each scalar, the length and the
cell-0 address of each span, the sink address, the expression temporaries, and the guard
registers of each nesting depth. Every scalar lives in a register. Span `t` stores cell `i`
little-endian in the eight bytes at `cellAddr p i`, where `p` is the value of register
`ptr t`; every cell occupies eight bytes whatever its declared width, which is the arena
layout for `w64` cells. The span's length is held in register `len t`; the four-byte arena
header before cell 0 is not read by the compiled code. `StateRel` states that the scalar
and length registers and the cells agree with an `FState`, and that distinct cells and the
sink cell occupy disjoint eight-byte ranges.

## Scope

`FExpr.fits`, `FStmt.fits` and `FProg.fits` state the compiled scope: no loops, every span
named is a span of the layout, every shift amount a literal below 64, every expression
scalar a register scalar of the layout, and every `matchTag` arm tag below `2^64`.

## Main definitions

* `Layout`, `LayoutOK`, `StateRel`: the data placement and the simulation relation.
* `compileExpr`, `compileStmt`, `compileArms`, `compileProg`: the compiler.
* `FExpr.fits`, `FStmt.fits`, `FProg.fits`: the compiled scope.

## Main results

* `compileExpr_correct`: expression code leaves the expression's value in its temporary
  and changes no other named register and no memory.
* `compileStmt_correct`, `compileArms_correct`: statement code under a guard holding `1`
  relates the state after the statement, and under a guard holding `0` the state before
  it.
* `compileProg_correct`: the result temporary is nonzero after the compiled program
  exactly when `FProg.run` answers `true`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem

/-! ## Machine steps -/

/-- The value of an operand in an address state. -/
def opv (s : AState) : JOperand → BitVec 64
  | .reg r => s.regs r
  | .imm v => BitVec.ofNat 64 v

/-- The register file `f` with register `d` set to `v`. -/
def upd (f : String → BitVec 64) (d : String) (v : BitVec 64) : String → BitVec 64 :=
  fun r => if r = d then v else f r

/-- The flags `cmp a, b` writes. -/
def cmpFlags (a b : BitVec 64) : RFlags :=
  { cf := (x86_CMP a b).cf, pf := (x86_CMP a b).pf, zf := (x86_CMP a b).zf,
    sf := (x86_CMP a b).sf, of := (x86_CMP a b).of }

/-- The address of cell `i` of a span whose cell 0 is at `p`: eight bytes per cell, the
offset formed as the indexed addressing mode forms it. -/
def cellAddr (p : BitVec 64) (i : Nat) : BitVec 64 := p + BitVec.ofInt 64 ((8 * i : Nat) : Int)

theorem evalA_mov (s : AState) (d : String) (o : JOperand) :
    evalInstrA s (.mov d o) = ⟨upd s.regs d (opv s o), s.flags, s.mem⟩ := by
  cases o <;> rfl

theorem evalA_cmp (s : AState) (a : String) (o : JOperand) :
    evalInstrA s (.cmp a o) = ⟨s.regs, cmpFlags (s.regs a) (opv s o), s.mem⟩ := by
  cases o <;> rfl

theorem evalA_cmovb (s : AState) (d : String) (o : JOperand) :
    evalInstrA s (.cmovb d o) =
      ⟨upd s.regs d (if s.flags.cf.getD false then opv s o else s.regs d), s.flags, s.mem⟩ := by
  cases o <;> rfl

theorem evalA_cmove (s : AState) (d : String) (o : JOperand) :
    evalInstrA s (.cmove d o) =
      ⟨upd s.regs d (if s.flags.zf.getD false then opv s o else s.regs d), s.flags, s.mem⟩ := by
  cases o <;> rfl

theorem evalA_cmovne (s : AState) (d : String) (o : JOperand) :
    evalInstrA s (.cmovne d o) =
      ⟨upd s.regs d (if (!s.flags.zf.getD false) = true then opv s o else s.regs d), s.flags,
        s.mem⟩ := by
  cases o <;> rfl

theorem evalA_loadMemIdx (s : AState) (d b i : String) :
    evalInstrA s (.loadMemIdx d b i 8) =
      ⟨upd s.regs d (read64 s.mem (cellAddr (s.regs b) (s.regs i).toNat)), s.flags, s.mem⟩ := by
  rfl

theorem evalA_storeMemIdx (s : AState) (b i : String) (o : JOperand) :
    evalInstrA s (.storeMemIdx b i 8 o) =
      ⟨s.regs, s.flags, write64 s.mem (cellAddr (s.regs b) (s.regs i).toNat) (opv s o)⟩ := by
  cases o <;> rfl

theorem evalA_and (s : AState) (d : String) (o : JOperand) :
    evalInstrA s (.and_ d o) =
      ⟨upd s.regs d (s.regs d &&& opv s o), (evalInstr s.view (.and_ d o)).flags, s.mem⟩ := by
  cases o <;> rfl

theorem cmpFlags_cf (a b : BitVec 64) : (cmpFlags a b).cf.getD false = decide (a < b) := by
  have ha := a.isLt
  have hb := b.isLt
  have key : ((a - b).toNat : Int) ≠ (a.toNat : Int) - (b.toNat : Int) ↔ a.toNat < b.toNat := by
    have hx : (a - b).toNat =
        if b.toNat ≤ a.toNat then a.toNat - b.toNat else 2 ^ 64 - b.toNat + a.toNat := by
      rw [BitVec.toNat_sub]; split <;> omega
    rw [hx]; split <;> omega
  simp only [cmpFlags, x86_CMP, x86_SUB, wunsigned, Option.getD_some, BitVec.lt_def]
  exact decide_eq_decide.mpr key

theorem cmpFlags_zf (a b : BitVec 64) : (cmpFlags a b).zf.getD false = decide (a = b) := by
  simp only [cmpFlags, x86_CMP, x86_SUB, ZF_of_word, Option.getD_some]
  have ha := a.isLt
  have hb := b.isLt
  by_cases h : a = b
  · subst h; simp
  · have : a.toNat ≠ b.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp only [h, decide_false, decide_eq_false_iff_not, BitVec.toNat_sub]
    omega

/-- The instruction computing `d := d op src` for an arithmetic or bitwise operator. -/
def arithInstr (op : FBinop) (d : String) (src : JOperand) : JInstr 64 :=
  match op with
  | .add => .add d src
  | .sub => .sub d src
  | .mul => .imul d src
  | .and => .and_ d src
  | .or => .or_ d src
  | .xor => .xor_ d src
  | .shl => .shl d src
  | .shr => .shr d src
  | _ => .mov d src

/-- The operators compiled by one register-to-register instruction. -/
def FBinop.isArith : FBinop → Bool
  | .add | .sub | .mul | .and | .or | .xor => true
  | _ => false

theorem evalA_arith (s : AState) (op : FBinop) (hop : op.isArith = true) (d : String)
    (o : JOperand) :
    evalInstrA s (arithInstr op d o) =
      ⟨upd s.regs d (op.eval (s.regs d) (opv s o)), (evalInstr s.view (arithInstr op d o)).flags,
        s.mem⟩ := by
  cases op <;> simp only [FBinop.isArith, Bool.false_eq_true] at hop <;> cases o <;> rfl

theorem shl_word (v : BitVec 64) (n : Nat) (hn : n < 64) :
    (x86_SHL v (BitVec.ofNat 64 n)).word = v <<< n := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by simp; omega
  simp only [x86_SHL, shiftCount, hn', CatCrypt.Crypto.SecureCompilation.VIR.shiftMask_of_lt hn]
  split
  · subst_vars; simp [rflags_None]
  · simp [rflags_OF, wshl, Nat.min_eq_right hn.le]

theorem shr_word (v : BitVec 64) (n : Nat) (hn : n < 64) :
    (x86_SHR v (BitVec.ofNat 64 n)).word = v >>> n := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by simp; omega
  simp only [x86_SHR, shiftCount, hn', CatCrypt.Crypto.SecureCompilation.VIR.shiftMask_of_lt hn]
  split
  · subst_vars; simp [rflags_None]
  · simp [rflags_OF, wshr, Nat.min_eq_right hn.le]

theorem evalA_shift (s : AState) (op : FBinop) (hop : op.isShift = true) (d : String) (n : Nat)
    (hn : n < 64) :
    evalInstrA s (arithInstr op d (.imm n)) =
      ⟨upd s.regs d (op.eval (s.regs d) (BitVec.ofNat 64 n)),
        (evalInstr s.view (arithInstr op d (.imm n))).flags, s.mem⟩ := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by simp; omega
  cases op <;> simp only [FBinop.isShift, Bool.false_eq_true] at hop
  · change (⟨upd s.regs d (x86_SHL (s.regs d) (BitVec.ofNat 64 n)).word, _, s.mem⟩ : AState) = _
    rw [shl_word _ _ hn]; simp only [FBinop.eval, hn']
  · change (⟨upd s.regs d (x86_SHR (s.regs d) (BitVec.ofNat 64 n)).word, _, s.mem⟩ : AState) = _
    rw [shr_word _ _ hn]; simp only [FBinop.eval, hn']

/-! ## Layout and simulation relation -/

/-- The registers the compiled code uses, by role: one per scalar, the length and the
cell-0 address of each span, the address of the sink cell, expression temporaries, and
the guard registers of nesting depth `k` (the guard of a `then` arm, of an `else` arm,
and the pair of a `matchTag`: the tag and the not-yet-matched flag). -/
inductive RegName
  | var (x : String)
  | len (s : String)
  | ptr (s : String)
  | sink
  | tmp (k : Nat)
  | gThen (k : Nat)
  | gElse (k : Nat)
  | gTag (k : Nat)
  deriving DecidableEq, Repr

/-- A data placement: a register name for each role, the scalars held in registers, and
the spans held in memory. Span `t` has its cells at `cellAddr p i`, where `p` is the value
of register `ptr t`: eight bytes per cell, cell 0 at `p`. Its length is held in register
`len t`. In the arena encoding the four-byte length header precedes cell 0. -/
structure Layout where
  name : RegName → String
  scalars : List String
  spans : List String

/-- The placement assigns distinct machine registers to distinct roles. -/
def LayoutOK (L : Layout) : Prop := Function.Injective L.name

/-- The register of temporary `k`. -/
def tR (L : Layout) (k : Nat) : String := L.name (.tmp k)

/-- Temporaries and guard registers; the others hold program data. -/
def RegName.scratch : RegName → Bool
  | .tmp _ | .gThen _ | .gElse _ | .gTag _ => true
  | _ => false

/-- The simulation relation. Each scalar's register holds its value; each span's length
register holds its length, which is below `2^64`; each cell reads back, little-endian at
`cellAddr`, as the cell's value; distinct cells occupy disjoint eight-byte ranges, and
the sink cell is disjoint from every cell. -/
structure StateRel (L : Layout) (σ : FState) (s : AState) : Prop where
  scalars : ∀ x ∈ L.scalars, s.regs (L.name (.var x)) = σ.scalars x
  len : ∀ t ∈ L.spans, s.regs (L.name (.len t)) = BitVec.ofNat 64 (σ.bufs t).length
  lenLt : ∀ t ∈ L.spans, (σ.bufs t).length < 2 ^ 64
  cells : ∀ t ∈ L.spans, ∀ i (h : i < (σ.bufs t).length),
    read64 s.mem (cellAddr (s.regs (L.name (.ptr t))) i) = (σ.bufs t)[i]
  sep : ∀ t ∈ L.spans, ∀ t' ∈ L.spans, ∀ i j, i < (σ.bufs t).length →
    j < (σ.bufs t').length → (t, i) ≠ (t', j) →
    Disjoint8 (cellAddr (s.regs (L.name (.ptr t))) i) (cellAddr (s.regs (L.name (.ptr t'))) j)
  sinkSep : ∀ t ∈ L.spans, ∀ i, i < (σ.bufs t).length →
    Disjoint8 (cellAddr (s.regs (L.name (.ptr t))) i) (s.regs (L.name .sink))

/-- The relation survives a step that keeps every data register and the memory. -/
theorem StateRel.frame {L : Layout} {σ : FState} {s s' : AState} (h : StateRel L σ s)
    (hr : ∀ n, n.scratch = false → s'.regs (L.name n) = s.regs (L.name n))
    (hm : s'.mem = s.mem) : StateRel L σ s' where
  scalars x hx := (hr (.var x) rfl).trans (h.scalars x hx)
  len t ht := (hr (.len t) rfl).trans (h.len t ht)
  lenLt := h.lenLt
  cells t ht i hi := by rw [hm, hr (.ptr t) rfl]; exact h.cells t ht i hi
  sep t ht t' ht' i j hi hj hne := by
    rw [hr (.ptr t) rfl, hr (.ptr t') rfl]; exact h.sep t ht t' ht' i j hi hj hne
  sinkSep t ht i hi := by rw [hr (.ptr t) rfl, hr .sink rfl]; exact h.sinkSep t ht i hi

/-! ## The expression compiler -/

/-- `d := d &&& mask w`, with temporary `d + 1` holding the mask. -/
def maskCode (L : Layout) (w : FWidth) (d : Nat) : List (JInstr 64) :=
  [.mov (tR L (d + 1)) (.imm (2 ^ w.bits - 1)), .and_ (tR L d) (.reg (tR L (d + 1)))]

/-- With an index in temporary `d`: temporary `d + 1` gets the cell-0 address of span `t`
and temporary `d + 2` the index when the index is below the length, and the sink address
and `0` otherwise; the carry flag records the comparison. -/
def selCode (L : Layout) (t : String) (d : Nat) : List (JInstr 64) :=
  [.mov (tR L (d + 1)) (.reg (L.name .sink)), .mov (tR L (d + 2)) (.imm 0),
   .cmp (tR L d) (.reg (L.name (.len t))),
   .cmovb (tR L (d + 1)) (.reg (L.name (.ptr t))), .cmovb (tR L (d + 2)) (.reg (tR L d))]

/-- With an index in temporary `d`: temporary `d` gets the cell at that index of span `t`
when the index is in range, and `0` otherwise. -/
def getCode (L : Layout) (t : String) (d : Nat) : List (JInstr 64) :=
  selCode L t d ++
    [.loadMemIdx (tR L (d + 3)) (tR L (d + 1)) (tR L (d + 2)) 8, .mov (tR L d) (.imm 0),
     .cmovb (tR L d) (.reg (tR L (d + 3)))]

/-- With operands in temporaries `d` and `d + 1`: temporary `d` gets `1` when the
comparison holds and `0` otherwise. -/
def cmpCode (L : Layout) (op : FBinop) (d : Nat) : List (JInstr 64) :=
  match op with
  | .lt => [.cmp (tR L d) (.reg (tR L (d + 1))), .mov (tR L d) (.imm 0),
      .mov (tR L (d + 2)) (.imm 1), .cmovb (tR L d) (.reg (tR L (d + 2)))]
  | .eq => [.cmp (tR L d) (.reg (tR L (d + 1))), .mov (tR L d) (.imm 0),
      .mov (tR L (d + 2)) (.imm 1), .cmove (tR L d) (.reg (tR L (d + 2)))]
  | .ule => [.cmp (tR L (d + 1)) (.reg (tR L d)), .mov (tR L d) (.imm 1),
      .mov (tR L (d + 2)) (.imm 0), .cmovb (tR L d) (.reg (tR L (d + 2)))]
  | _ => []

/-- With a value in temporary `d`: temporary `d` gets `1` when the value is `0`, and `0`
otherwise. -/
def notCode (L : Layout) (d : Nat) : List (JInstr 64) :=
  [.mov (tR L (d + 1)) (.imm 0), .cmp (tR L d) (.reg (tR L (d + 1))), .mov (tR L d) (.imm 0),
   .mov (tR L (d + 1)) (.imm 1), .cmove (tR L d) (.reg (tR L (d + 1)))]

/-- The code leaving the value of an expression in temporary `d`, using temporaries
`d` and above and writing no other register and no memory. A shift by a non-literal
amount compiles to the empty block and is excluded by `FExpr.fits`. -/
def compileExpr (L : Layout) (Γ : String → FWidth) (d : Nat) : FExpr → List (JInstr 64)
  | .var x => [.mov (tR L d) (.reg (L.name (.var x)))]
  | .lit n => [.mov (tR L d) (.imm n)]
  | .bin op a b =>
      if op.isCompare then compileExpr L Γ d a ++ compileExpr L Γ (d + 1) b ++ cmpCode L op d
      else if op.isShift then
        match b with
        | .lit n => compileExpr L Γ d a ++ [arithInstr op (tR L d) (.imm n)] ++
            maskCode L (((FExpr.bin op a b).width Γ).getD .w64) d
        | _ => []
      else compileExpr L Γ d a ++ compileExpr L Γ (d + 1) b ++
        [arithInstr op (tR L d) (.reg (tR L (d + 1)))] ++
        maskCode L (((FExpr.bin op a b).width Γ).getD .w64) d
  | .not a => compileExpr L Γ d a ++ notCode L d
  | .spanLen t => [.mov (tR L d) (.reg (L.name (.len t)))]
  | .spanGet t i => compileExpr L Γ d i ++ getCode L t d
  | .tagOf t => .mov (tR L d) (.imm 0) :: getCode L t d
  | .payload t => .mov (tR L d) (.imm 1) :: getCode L t d

/-- The expression is in the compiled scope for layout `L`: every scalar it reads is a
register scalar of `L`, every span it reads is a span of `L`, and every shift amount is
a literal below 64. -/
def FExpr.fits (L : Layout) : FExpr → Bool
  | .var x => decide (x ∈ L.scalars)
  | .lit _ => true
  | .bin op a b =>
      if op.isShift then
        (match b with
          | .lit n => decide (n < 64)
          | _ => false) && a.fits L
      else a.fits L && b.fits L
  | .not a => a.fits L
  | .spanLen t => decide (t ∈ L.spans)
  | .spanGet t i => decide (t ∈ L.spans) && i.fits L
  | .tagOf t => decide (t ∈ L.spans)
  | .payload t => decide (t ∈ L.spans)

theorem lt_ofNat_iff (v : BitVec 64) (n : Nat) (hn : n < 2 ^ 64) :
    v < BitVec.ofNat 64 n ↔ v.toNat < n := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- Every named register other than the temporaries from `d` up, and the memory, are the
same in `s` and `s'`. -/
def TmpFrame (L : Layout) (d : Nat) (s s' : AState) : Prop :=
  (∀ n, (∀ k, d ≤ k → n ≠ .tmp k) → s'.regs (L.name n) = s.regs (L.name n)) ∧ s'.mem = s.mem

/-- The postcondition of expression code at temporary `d`: temporary `d` holds `v`, and
`TmpFrame L d` relates the entry and exit states. -/
def ExprPost (L : Layout) (d : Nat) (v : BitVec 64) (s s' : AState) : Prop :=
  s'.regs (tR L d) = v ∧ TmpFrame L d s s'

theorem TmpFrame.trans {L : Layout} {d : Nat} {s s1 s2 : AState} (h1 : TmpFrame L d s s1)
    (h2 : TmpFrame L d s1 s2) : TmpFrame L d s s2 :=
  ⟨fun n hn => (h2.1 n hn).trans (h1.1 n hn), h2.2.trans h1.2⟩

theorem TmpFrame.succ {L : Layout} {d : Nat} {s s' : AState} (h : TmpFrame L (d + 1) s s') :
    TmpFrame L d s s' :=
  ⟨fun n hn => h.1 n (fun k hk => hn k (by omega)), h.2⟩

theorem TmpFrame.tmp_self {L : Layout} {d : Nat} {s s' : AState} (h : TmpFrame L (d + 1) s s') :
    s'.regs (tR L d) = s.regs (tR L d) :=
  h.1 (.tmp d) (fun k hk e => by cases e; omega)

theorem TmpFrame.stateRel {L : Layout} {d : Nat} {σ : FState} {s s' : AState}
    (hR : StateRel L σ s) (h : TmpFrame L d s s') : StateRel L σ s' :=
  hR.frame (fun n hn => h.1 n (fun k _ e => by subst e; simp [RegName.scratch] at hn)) h.2

theorem getCode_correct {L : Layout} (hL : LayoutOK L) {σ : FState} {s : AState}
    (hR : StateRel L σ s) {t : String} (ht : t ∈ L.spans) (d : Nat) :
    ExprPost L d ((σ.bufs t).getD (s.regs (tR L d)).toNat 0) s (runBlockA s (getCode L t d)) := by
  simp only [getCode, selCode, List.cons_append, List.nil_append, runBlockA_cons, runBlockA_nil,
    evalA_mov, evalA_cmp, evalA_cmovb, evalA_loadMemIdx]
  refine ⟨?_, ?_, rfl⟩
  · simp only [tR, upd, opv, hL.eq_iff, cmpFlags_cf, hR.len t ht]
    simp
    by_cases h : s.regs (L.name (.tmp d)) < BitVec.ofNat 64 (σ.bufs t).length
    · have h' := (lt_ofNat_iff _ _ (hR.lenLt t ht)).1 h
      simp [h, hR.cells t ht _ h', List.getElem?_eq_getElem h']
    · have h' := mt (lt_ofNat_iff _ _ (hR.lenLt t ht)).2 h
      simp [h, List.getElem?_eq_none (Nat.le_of_not_lt h')]
  · intro n hn
    have h0 := hn d (by omega)
    have h1 := hn (d + 1) (by omega)
    have h2 := hn (d + 2) (by omega)
    have h3 := hn (d + 3) (by omega)
    simp [tR, upd, hL.eq_iff, h0, h1, h2, h3]

theorem arithTail_correct {L : Layout} (hL : LayoutOK L) (op : FBinop) (hop : op.isArith = true)
    (w : FWidth) (d : Nat) (s : AState) :
    ExprPost L d (op.eval (s.regs (tR L d)) (s.regs (tR L (d + 1))) &&& w.mask) s
      (runBlockA s ([arithInstr op (tR L d) (.reg (tR L (d + 1)))] ++ maskCode L w d)) := by
  simp only [maskCode, List.cons_append, List.nil_append, runBlockA_cons, runBlockA_nil,
    evalA_arith s op hop, evalA_mov, evalA_and]
  refine ⟨?_, ?_, rfl⟩
  · simp [tR, upd, opv, hL.eq_iff, FWidth.mask]
  · intro n hn
    have h0 := hn d (by omega)
    have h1 := hn (d + 1) (by omega)
    simp [tR, upd, hL.eq_iff, h0, h1]

theorem shiftTail_correct {L : Layout} (hL : LayoutOK L) (op : FBinop) (hop : op.isShift = true)
    (n : Nat) (hn : n < 64) (w : FWidth) (d : Nat) (s : AState) :
    ExprPost L d (op.eval (s.regs (tR L d)) (BitVec.ofNat 64 n) &&& w.mask) s
      (runBlockA s ([arithInstr op (tR L d) (.imm n)] ++ maskCode L w d)) := by
  simp only [maskCode, List.cons_append, List.nil_append, runBlockA_cons, runBlockA_nil,
    evalA_shift s op hop _ n hn, evalA_mov, evalA_and]
  refine ⟨?_, ?_, rfl⟩
  · simp [tR, upd, opv, hL.eq_iff, FWidth.mask]
  · intro n hn
    have h0 := hn d (by omega)
    have h1 := hn (d + 1) (by omega)
    simp [tR, upd, hL.eq_iff, h0, h1]

theorem cmpTail_correct {L : Layout} (hL : LayoutOK L) (op : FBinop) (hop : op.isCompare = true)
    (d : Nat) (s : AState) :
    ExprPost L d (op.eval (s.regs (tR L d)) (s.regs (tR L (d + 1)))) s
      (runBlockA s (cmpCode L op d)) := by
  cases op <;> simp only [FBinop.isCompare, Bool.false_eq_true] at hop <;>
    simp only [cmpCode, runBlockA_cons, runBlockA_nil, evalA_mov, evalA_cmp, evalA_cmovb,
      evalA_cmove] <;>
    refine ⟨?_, ?_, rfl⟩
  · simp only [tR, upd, opv, hL.eq_iff, cmpFlags_cf]
    simp [FBinop.eval]
  · intro n hn
    have h0 := hn d (by omega)
    have h2 := hn (d + 2) (by omega)
    simp [tR, upd, hL.eq_iff, h0, h2]
  · simp only [tR, upd, opv, hL.eq_iff, cmpFlags_zf]
    simp [FBinop.eval]
  · intro n hn
    have h0 := hn d (by omega)
    have h2 := hn (d + 2) (by omega)
    simp [tR, upd, hL.eq_iff, h0, h2]
  · simp only [tR, upd, opv, hL.eq_iff, cmpFlags_cf]
    simp [FBinop.eval]
    by_cases h : s.regs (L.name (RegName.tmp (d + 1))) < s.regs (L.name (RegName.tmp d)) <;>
      simp [h, BitVec.not_lt.mp, BitVec.not_le.mpr]
  · intro n hn
    have h0 := hn d (by omega)
    have h2 := hn (d + 2) (by omega)
    simp [tR, upd, hL.eq_iff, h0, h2]

theorem notTail_correct {L : Layout} (hL : LayoutOK L) (d : Nat) (s : AState) :
    ExprPost L d (if s.regs (tR L d) = 0 then 1 else 0) s (runBlockA s (notCode L d)) := by
  simp only [notCode, runBlockA_cons, runBlockA_nil, evalA_mov, evalA_cmp, evalA_cmove]
  refine ⟨?_, ?_, rfl⟩
  · simp only [tR, upd, opv, hL.eq_iff, cmpFlags_zf]
    simp
    exact if_congr Iff.rfl rfl rfl
  · intro n hn
    have h0 := hn d (by omega)
    have h1 := hn (d + 1) (by omega)
    simp [tR, upd, hL.eq_iff, h0, h1]

/-! ## The statement compiler

Statements compile branch-free under a guard register holding `1` (the statement runs) or
`0` (it has no effect). An assignment writes its scalar register through `cmovne` on the
guard; a span store is redirected to the sink cell when the guard is `0` or the index is
out of range. `ite` and `matchTag` evaluate their selector once, set the guard registers
of the next depth, and compile every arm under its own guard. Code at depth `k` writes the
temporaries, the scalar registers and the guard registers of depths above `k`. -/

/-- A guarded assignment: the value, masked to the scalar's width, is written to the
scalar's register when guard `g` is nonzero. -/
def assignCode (L : Layout) (Γ : String → FWidth) (g : RegName) (x : String) (e : FExpr) :
    List (JInstr 64) :=
  compileExpr L Γ 0 e ++ maskCode L (Γ x) 0 ++
    [.mov (tR L 1) (.imm 0), .cmp (L.name g) (.reg (tR L 1)),
     .cmovne (L.name (.var x)) (.reg (tR L 0))]

/-- A guarded span store: the masked value goes to the cell at the index when guard `g` is
nonzero and the index is in range, and to the sink cell otherwise. -/
def setCode (L : Layout) (Γ : String → FWidth) (g : RegName) (t : String) (i v : FExpr) :
    List (JInstr 64) :=
  compileExpr L Γ 0 v ++ maskCode L (Γ t) 0 ++ compileExpr L Γ 1 i ++ selCode L t 1 ++
    [.mov (tR L 4) (.imm 0), .cmp (L.name g) (.reg (tR L 4)),
     .cmove (tR L 2) (.reg (L.name .sink)), .cmove (tR L 3) (.reg (tR L 4)),
     .storeMemIdx (tR L 2) (tR L 3) 8 (.reg (tR L 0))]

/-- With a condition in temporary 0 and guard `g`: the `then` guard of depth `k + 1` gets
`g` when the condition is nonzero and `0` otherwise, and the `else` guard the converse. -/
def iteGuards (L : Layout) (g : RegName) (k : Nat) : List (JInstr 64) :=
  [.mov (tR L 1) (.imm 0), .cmp (tR L 0) (.reg (tR L 1)),
   .mov (L.name (.gThen (k + 1))) (.reg (L.name g)),
   .cmove (L.name (.gThen (k + 1))) (.reg (tR L 1)),
   .mov (L.name (.gElse (k + 1))) (.imm 0),
   .cmove (L.name (.gElse (k + 1))) (.reg (L.name g))]

/-- With the tag in `gTag (k + 1)` and the not-yet-matched flag in `gElse (k + 1)`: the arm
guard `gThen (k + 1)` gets the flag when the tag is `tag` and `0` otherwise, and the flag
is cleared when the tag is `tag`. -/
def armGuards (L : Layout) (k tag : Nat) : List (JInstr 64) :=
  [.mov (tR L 0) (.imm tag), .cmp (L.name (.gTag (k + 1))) (.reg (tR L 0)),
   .mov (tR L 1) (.imm 0),
   .mov (L.name (.gThen (k + 1))) (.imm 0),
   .cmove (L.name (.gThen (k + 1))) (.reg (L.name (.gElse (k + 1)))),
   .cmove (L.name (.gElse (k + 1))) (.reg (tR L 1))]

/-- With guard `g`: `gTag (k + 1)` gets the tag of `t` and `gElse (k + 1)` gets `g`. -/
def matchPrologue (L : Layout) (g : RegName) (k : Nat) (t : String) : List (JInstr 64) :=
  (.mov (tR L 0) (.imm 0) :: getCode L t 0) ++
    [.mov (L.name (.gTag (k + 1))) (.reg (tR L 0)), .mov (L.name (.gElse (k + 1))) (.reg (L.name g))]

mutual

/-- The code of a statement at nesting depth `k` under guard register `g`. Loops compile
to the empty block and are excluded by `FStmt.fits`. -/
def compileStmt (L : Layout) (Γ : String → FWidth) : Nat → RegName → FStmt → List (JInstr 64)
  | _, _, .skip => []
  | k, g, .seq a b => compileStmt L Γ k g a ++ compileStmt L Γ k g b
  | _, g, .assign x e => assignCode L Γ g x e
  | _, g, .spanSet t i v => setCode L Γ g t i v
  | k, g, .ite c a b =>
      compileExpr L Γ 0 c ++ iteGuards L g k ++ compileStmt L Γ (k + 1) (.gThen (k + 1)) a ++
        compileStmt L Γ (k + 1) (.gElse (k + 1)) b
  | k, g, .matchTag t arms dflt =>
      matchPrologue L g k t ++ compileArms L Γ k arms ++
        compileStmt L Γ (k + 1) (.gElse (k + 1)) dflt
  | _, _, .forLit .. => []
  | _, _, .forLen .. => []

/-- The code of the arms of a `matchTag` at depth `k`. -/
def compileArms (L : Layout) (Γ : String → FWidth) (k : Nat) :
    List (Nat × FStmt) → List (JInstr 64)
  | [] => []
  | (tag, b) :: rest =>
      armGuards L k tag ++ compileStmt L Γ (k + 1) (.gThen (k + 1)) b ++ compileArms L Γ k rest

end

mutual

/-- The statement is in the compiled scope for layout `L`: it has no loop, every span it
names is a span of `L`, every expression fits, and every `matchTag` arm tag is below
`2^64`. -/
def FStmt.fits (L : Layout) : FStmt → Bool
  | .skip => true
  | .seq a b => a.fits L && b.fits L
  | .assign _ e => e.fits L
  | .spanSet t i v => decide (t ∈ L.spans) && i.fits L && v.fits L
  | .ite c a b => c.fits L && a.fits L && b.fits L
  | .matchTag t arms dflt => decide (t ∈ L.spans) && FStmt.fitsArms L arms && dflt.fits L
  | .forLit .. => false
  | .forLen .. => false

/-- Every arm is in the compiled scope and has a tag below `2^64`. -/
def FStmt.fitsArms (L : Layout) : List (Nat × FStmt) → Bool
  | [] => true
  | (tag, b) :: rest => decide (tag < 2 ^ 64) && b.fits L && FStmt.fitsArms L rest

end

/-- The compiled program: set the depth-0 guard to `1`, run the body, and leave the value
of the result expression in temporary 0. -/
def compileProg (L : Layout) (p : FProg) : List (JInstr 64) :=
  .mov (L.name (.gThen 0)) (.imm 1) :: compileStmt L p.widths 0 (.gThen 0) p.body ++
    compileExpr L p.widths 0 p.result

/-- The program is in the compiled scope for layout `L`. -/
def FProg.fits (L : Layout) (p : FProg) : Bool := p.body.fits L && p.result.fits L

/-! ## Correctness of the expression compiler -/

theorem movTmp_post {L : Layout} (hL : LayoutOK L) (d : Nat) (s : AState) (o : JOperand) :
    ExprPost L d (opv s o) s (evalInstrA s (.mov (tR L d) o)) := by
  rw [evalA_mov]
  refine ⟨by simp [upd], ?_, rfl⟩
  intro n hn
  have h0 := hn d le_rfl
  simp [tR, upd, hL.eq_iff, h0]

theorem FBinop.isArith_of {op : FBinop} (hc : op.isCompare = false) (hs : op.isShift = false) :
    op.isArith = true := by
  cases op <;> simp_all [FBinop.isCompare, FBinop.isShift, FBinop.isArith]

theorem FBinop.isShift_of_isCompare {op : FBinop} (hc : op.isCompare = true) :
    op.isShift = false := by
  cases op <;> simp_all [FBinop.isCompare, FBinop.isShift]

/-- **Expression compiler correctness.** For an expression in scope, the compiled code
leaves the expression's value in temporary `d`, changes no named register other than the
temporaries from `d` up, and changes no memory. -/
theorem compileExpr_correct {L : Layout} (hL : LayoutOK L) (Γ : String → FWidth) {σ : FState} :
    ∀ (e : FExpr) (d : Nat) (s : AState), e.fits L = true → StateRel L σ s →
      ExprPost L d (e.eval Γ σ) s (runBlockA s (compileExpr L Γ d e))
  | .var x, d, s, hf, hR => by
      simp only [FExpr.fits, decide_eq_true_eq] at hf
      have h := movTmp_post hL d s (.reg (L.name (.var x)))
      simp only [opv, hR.scalars x hf] at h
      exact h
  | .lit n, d, s, _, _ => movTmp_post hL d s (.imm n)
  | .spanLen t, d, s, hf, hR => by
      simp only [FExpr.fits, decide_eq_true_eq] at hf
      have h := movTmp_post hL d s (.reg (L.name (.len t)))
      simp only [opv, hR.len t hf] at h
      exact h
  | .bin op a b, d, s, hf, hR => by
      by_cases hc : op.isCompare = true
      · have hs := FBinop.isShift_of_isCompare hc
        simp only [FExpr.fits, hs, Bool.false_eq_true, if_false, Bool.and_eq_true] at hf
        simp only [compileExpr, hc, if_true, runBlockA_append]
        obtain ⟨ha1, ha2⟩ := compileExpr_correct hL Γ a d s hf.1 hR
        obtain ⟨hb1, hb2⟩ := compileExpr_correct hL Γ b (d + 1) _ hf.2 (ha2.stateRel hR)
        obtain ⟨hc1, hc2⟩ := cmpTail_correct hL op hc d
          (runBlockA (runBlockA s (compileExpr L Γ d a)) (compileExpr L Γ (d + 1) b))
        refine ⟨?_, ha2.trans (hb2.succ.trans hc2)⟩
        rw [hc1, hb1, hb2.tmp_self, ha1]
        simp [FExpr.eval, hc]
      · simp only [Bool.not_eq_true] at hc
        by_cases hs : op.isShift = true
        · cases b with
          | lit n =>
            simp only [FExpr.fits, hs, if_true, Bool.and_eq_true, decide_eq_true_eq] at hf
            simp only [compileExpr, hc, hs, Bool.false_eq_true, if_false, if_true,
              runBlockA_append]
            obtain ⟨ha1, ha2⟩ := compileExpr_correct hL Γ a d s hf.2 hR
            obtain ⟨hc1, hc2⟩ := shiftTail_correct hL op hs n hf.1
              (((FExpr.bin op a (.lit n)).width Γ).getD .w64) d (runBlockA s (compileExpr L Γ d a))
            rw [runBlockA_append] at hc1 hc2
            refine ⟨?_, ha2.trans hc2⟩
            rw [hc1, ha1]
            simp [FExpr.eval, hc]
          | _ => simp [FExpr.fits, hs] at hf
        · simp only [Bool.not_eq_true] at hs
          have har := FBinop.isArith_of hc hs
          simp only [FExpr.fits, hs, Bool.false_eq_true, if_false, Bool.and_eq_true] at hf
          simp only [compileExpr, hc, hs, Bool.false_eq_true, if_false, runBlockA_append]
          obtain ⟨ha1, ha2⟩ := compileExpr_correct hL Γ a d s hf.1 hR
          obtain ⟨hb1, hb2⟩ := compileExpr_correct hL Γ b (d + 1) _ hf.2 (ha2.stateRel hR)
          obtain ⟨hc1, hc2⟩ := arithTail_correct hL op har
            (((FExpr.bin op a b).width Γ).getD .w64) d
            (runBlockA (runBlockA s (compileExpr L Γ d a)) (compileExpr L Γ (d + 1) b))
          rw [runBlockA_append] at hc1 hc2
          refine ⟨?_, ha2.trans (hb2.succ.trans hc2)⟩
          rw [hc1, hb1, hb2.tmp_self, ha1]
          simp [FExpr.eval, hc]
  | .not a, d, s, hf, hR => by
      simp only [FExpr.fits] at hf
      simp only [compileExpr, runBlockA_append]
      obtain ⟨ha1, ha2⟩ := compileExpr_correct hL Γ a d s hf hR
      obtain ⟨hc1, hc2⟩ := notTail_correct hL d (runBlockA s (compileExpr L Γ d a))
      refine ⟨?_, ha2.trans hc2⟩
      rw [hc1, ha1]
      simp only [FExpr.eval]
  | .spanGet t i, d, s, hf, hR => by
      simp only [FExpr.fits, Bool.and_eq_true, decide_eq_true_eq] at hf
      simp only [compileExpr, runBlockA_append]
      obtain ⟨ha1, ha2⟩ := compileExpr_correct hL Γ i d s hf.2 hR
      obtain ⟨hc1, hc2⟩ := getCode_correct hL (ha2.stateRel hR) hf.1 d
      refine ⟨?_, ha2.trans hc2⟩
      rw [hc1, ha1]
      rfl
  | .tagOf t, d, s, hf, hR => by
      simp only [FExpr.fits, decide_eq_true_eq] at hf
      simp only [compileExpr, runBlockA_cons]
      obtain ⟨ha1, ha2⟩ := movTmp_post hL d s (.imm 0)
      obtain ⟨hc1, hc2⟩ := getCode_correct hL (ha2.stateRel hR) hf d
      refine ⟨?_, ha2.trans hc2⟩
      rw [hc1, ha1]
      simp [opv, FExpr.eval]
  | .payload t, d, s, hf, hR => by
      simp only [FExpr.fits, decide_eq_true_eq] at hf
      simp only [compileExpr, runBlockA_cons]
      obtain ⟨ha1, ha2⟩ := movTmp_post hL d s (.imm 1)
      obtain ⟨hc1, hc2⟩ := getCode_correct hL (ha2.stateRel hR) hf d
      refine ⟨?_, ha2.trans hc2⟩
      rw [hc1, ha1]
      simp [opv, FExpr.eval]

/-! ## Updates of the relation -/

theorem FState.setBuf_self (σ : FState) (t : String) : σ.setBuf t (σ.bufs t) = σ := by
  cases σ
  simp only [FState.setBuf, FState.mk.injEq, true_and]
  funext u
  split <;> simp_all

/-- Writing a scalar's register with a new value relates the state with that scalar
updated. -/
theorem StateRel.setScalar {L : Layout} {σ : FState} {s s' : AState}
    (hR : StateRel L σ s) (x : String) (v : BitVec 64)
    (hr : ∀ n, n.scratch = false → n ≠ .var x → s'.regs (L.name n) = s.regs (L.name n))
    (hx : s'.regs (L.name (.var x)) = v) (hm : s'.mem = s.mem) :
    StateRel L (σ.set x v) s' where
  scalars y hy := by
    by_cases h : y = x
    · subst h; simp [FState.set, hx]
    · rw [hr (.var y) rfl (by simp [h])]
      simp [FState.set, h, hR.scalars y hy]
  len t ht := (hr (.len t) rfl (by simp)).trans (hR.len t ht)
  lenLt := hR.lenLt
  cells t ht i hi := by
    rw [hm, hr (.ptr t) rfl (by simp)]; exact hR.cells t ht i hi
  sep t ht t' ht' i j hi hj hne := by
    rw [hr (.ptr t) rfl (by simp), hr (.ptr t') rfl (by simp)]
    exact hR.sep t ht t' ht' i j hi hj hne
  sinkSep t ht i hi := by
    rw [hr (.ptr t) rfl (by simp), hr .sink rfl (by simp)]; exact hR.sinkSep t ht i hi

/-- A store to cell `i` of span `t`, in range, relates the state with that cell updated. -/
theorem StateRel.store {L : Layout} {σ : FState} {s s' : AState} (hR : StateRel L σ s)
    {t : String} (ht : t ∈ L.spans) {i : Nat} (hi : i < (σ.bufs t).length) (v : BitVec 64)
    (hr : ∀ n, n.scratch = false → s'.regs (L.name n) = s.regs (L.name n))
    (hm : s'.mem = write64 s.mem (cellAddr (s.regs (L.name (.ptr t))) i) v) :
    StateRel L (σ.setBuf t ((σ.bufs t).set i v)) s' := by
  have hlen : ∀ u, ((σ.setBuf t ((σ.bufs t).set i v)).bufs u).length = (σ.bufs u).length := by
    intro u; simp only [FState.setBuf]; split <;> simp_all
  refine ⟨fun x hx => (hr (.var x) rfl).trans (hR.scalars x hx), ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu; rw [hr (.len u) rfl, hlen]; exact hR.len u hu
  · intro u hu; rw [hlen]; exact hR.lenLt u hu
  · intro u hu j hj
    have hj' := hj
    rw [hlen] at hj'
    rw [hm, hr (.ptr u) rfl]
    by_cases h : (u, j) = (t, i)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [read64_write64_same]
      simp [FState.setBuf]
    · rw [read64_write64_of_disjoint _ _ _ _ (hR.sep t ht u hu i j hi hj' (Ne.symm h)),
        hR.cells u hu j hj']
      simp only [FState.setBuf]
      split
      · subst_vars
        rw [List.getElem_set_ne]
        intro e; exact h (by rw [e])
      · rfl
  · intro u hu u' hu' j j' hj hj' hne
    rw [hlen] at hj hj'
    rw [hr (.ptr u) rfl, hr (.ptr u') rfl]
    exact hR.sep u hu u' hu' j j' hj hj' hne
  · intro u hu j hj
    rw [hlen] at hj
    rw [hr (.ptr u) rfl, hr .sink rfl]
    exact hR.sinkSep u hu j hj

/-- A store to the sink cell keeps the relation. -/
theorem StateRel.storeSink {L : Layout} {σ : FState} {s s' : AState} (hR : StateRel L σ s)
    (v : BitVec 64)
    (hr : ∀ n, n.scratch = false → s'.regs (L.name n) = s.regs (L.name n))
    (hm : s'.mem = write64 s.mem (s.regs (L.name .sink)) v) : StateRel L σ s' := by
  refine ⟨fun x hx => (hr (.var x) rfl).trans (hR.scalars x hx),
    fun u hu => (hr (.len u) rfl).trans (hR.len u hu), hR.lenLt, ?_, ?_, ?_⟩
  · intro u hu j hj
    rw [hm, hr (.ptr u) rfl, read64_write64_of_disjoint _ _ _ _ (hR.sinkSep u hu j hj).symm]
    exact hR.cells u hu j hj
  · intro u hu u' hu' j j' hj hj' hne
    rw [hr (.ptr u) rfl, hr (.ptr u') rfl]
    exact hR.sep u hu u' hu' j j' hj hj' hne
  · intro u hu j hj
    rw [hr (.ptr u) rfl, hr .sink rfl]
    exact hR.sinkSep u hu j hj

/-! ## Correctness of the statement compiler -/

/-- The registers code at depth `k` may write: temporaries, scalar registers, and guard
registers of depths above `k`. -/
def RegName.written (k : Nat) : RegName → Bool
  | .tmp _ | .var _ => true
  | .gThen j | .gElse j | .gTag j => decide (k < j)
  | _ => false

/-- A guard register of depth at most `k`. -/
def RegName.guardAt (k : Nat) : RegName → Bool
  | .gThen j | .gElse j => decide (j ≤ k)
  | _ => false

/-- Every named register that code at depth `k` does not write is the same in `s` and
`s'`. -/
def StmtFrame (L : Layout) (k : Nat) (s s' : AState) : Prop :=
  ∀ n, n.written k = false → s'.regs (L.name n) = s.regs (L.name n)

theorem StmtFrame.trans {L : Layout} {k : Nat} {s s1 s2 : AState} (h1 : StmtFrame L k s s1)
    (h2 : StmtFrame L k s1 s2) : StmtFrame L k s s2 :=
  fun n hn => (h2 n hn).trans (h1 n hn)

theorem StmtFrame.succ {L : Layout} {k : Nat} {s s' : AState} (h : StmtFrame L (k + 1) s s') :
    StmtFrame L k s s' := by
  intro n hn
  apply h n
  cases n <;> simp_all [RegName.written] <;> omega

theorem TmpFrame.stmtFrame {L : Layout} {d k : Nat} {s s' : AState} (h : TmpFrame L d s s') :
    StmtFrame L k s s' :=
  fun n hn => h.1 n (fun j _ e => by subst e; simp [RegName.written] at hn)

theorem RegName.written_of_guardAt {k : Nat} {g : RegName} (h : g.guardAt k = true) :
    g.written k = false := by
  cases g <;> simp_all [RegName.guardAt, RegName.written]

theorem RegName.not_tmp_of_guardAt {k : Nat} {g : RegName} (h : g.guardAt k = true) (j : Nat) :
    g ≠ .tmp j := by
  rintro rfl; simp [RegName.guardAt] at h

theorem maskTail_correct {L : Layout} (hL : LayoutOK L) (w : FWidth) (d : Nat) (s : AState) :
    ExprPost L d (s.regs (tR L d) &&& w.mask) s (runBlockA s (maskCode L w d)) := by
  simp only [maskCode, runBlockA_cons, runBlockA_nil, evalA_mov, evalA_and]
  refine ⟨?_, ?_, rfl⟩
  · simp [tR, upd, opv, hL.eq_iff, FWidth.mask]
  · intro n hn
    have h0 := hn d (by omega)
    have h1 := hn (d + 1) (by omega)
    simp [tR, upd, hL.eq_iff, h0, h1]

/-- **Guarded assignment.** Under a guard holding `1` the code relates the state after the
assignment, and under a guard holding `0` the state before it. -/
theorem assignCode_correct {L : Layout} (hL : LayoutOK L) (Γ : String → FWidth) {σ : FState}
    {s : AState} {k : Nat} {g : RegName} (hg : g.guardAt k = true) (b : Bool)
    (hgv : s.regs (L.name g) = if b then 1 else 0) {x : String} {e : FExpr}
    (he : e.fits L = true) (hR : StateRel L σ s) :
    StateRel L (if b then (FStmt.assign x e).exec Γ σ else σ)
        (runBlockA s (assignCode L Γ g x e)) ∧
      StmtFrame L k s (runBlockA s (assignCode L Γ g x e)) := by
  simp only [assignCode, runBlockA_append]
  obtain ⟨h1, h2⟩ := compileExpr_correct hL Γ e 0 s he hR
  obtain ⟨m1, m2⟩ := maskTail_correct hL (Γ x) 0 (runBlockA s (compileExpr L Γ 0 e))
  have f := h2.trans m2
  generalize runBlockA (runBlockA s (compileExpr L Γ 0 e)) (maskCode L (Γ x) 0) = s2 at m1 f
  rw [h1] at m1
  have hg2 : s2.regs (L.name g) = if b then 1 else 0 :=
    (f.1 g (fun j _ => RegName.not_tmp_of_guardAt hg j)).trans hgv
  have hR2 : StateRel L σ s2 := f.stateRel hR
  have hgt : ∀ j, g ≠ .tmp j := RegName.not_tmp_of_guardAt hg
  generalize hs3 : runBlockA s2 [.mov (tR L 1) (.imm 0), .cmp (L.name g) (.reg (tR L 1)),
     .cmovne (L.name (.var x)) (.reg (tR L 0))] = s3
  have e1 : s3.regs (L.name (.var x)) =
      if b then (e.eval Γ σ &&& (Γ x).mask) else s2.regs (L.name (.var x)) := by
    subst hs3
    simp only [runBlockA_cons, runBlockA_nil, evalA_mov, evalA_cmp, evalA_cmovne]
    simp only [tR, upd, opv, hL.eq_iff, cmpFlags_zf]
    simp only [tR] at m1
    cases b <;> simp [hgt, hg2, m1]
  have e2 : ∀ n, n ≠ .var x → (∀ j, n ≠ .tmp j) → s3.regs (L.name n) = s.regs (L.name n) := by
    intro n hx' hn
    subst hs3
    simp only [runBlockA_cons, runBlockA_nil, evalA_mov, evalA_cmp, evalA_cmovne]
    simp only [tR, upd, hL.eq_iff, hx', hn, if_false]
    exact f.1 n (fun j _ => hn j)
  have e3 : s3.mem = s2.mem := by
    subst hs3; rfl
  have fx : StmtFrame L k s s3 := by
    intro n hn
    have hx' : n ≠ .var x := by rintro rfl; simp [RegName.written] at hn
    exact e2 n hx' (fun j e => by subst e; simp [RegName.written] at hn)
  refine ⟨?_, fx⟩
  cases b
  · refine hR2.frame (fun n hn => ?_) e3
    by_cases hxn : n = .var x
    · subst hxn; simpa using e1
    · rw [e2 n hxn (fun j e => by subst e; simp [RegName.scratch] at hn)]
      exact (f.1 n (fun j _ e => by subst e; simp [RegName.scratch] at hn)).symm
  · refine hR2.setScalar x _ (fun n hn hxn => ?_) (by simpa using e1) e3
    rw [e2 n hxn (fun j e => by subst e; simp [RegName.scratch] at hn)]
    exact (f.1 n (fun j _ e => by subst e; simp [RegName.scratch] at hn)).symm

theorem cellAddr_zero (p : BitVec 64) : cellAddr p 0 = p := by simp [cellAddr]

/-- **Guarded span store.** Under a guard holding `1` the code relates the state after the
store, and under a guard holding `0` the state before it. An out-of-range index writes the
sink cell, and `List.set` leaves the span unchanged. -/
theorem setCode_correct {L : Layout} (hL : LayoutOK L) (Γ : String → FWidth) {σ : FState}
    {s : AState} {k : Nat} {g : RegName} (hg : g.guardAt k = true) (b : Bool)
    (hgv : s.regs (L.name g) = if b then 1 else 0) {t : String} {i v : FExpr}
    (ht : t ∈ L.spans) (hi : i.fits L = true) (hv : v.fits L = true) (hR : StateRel L σ s) :
    StateRel L (if b then (FStmt.spanSet t i v).exec Γ σ else σ)
        (runBlockA s (setCode L Γ g t i v)) ∧
      StmtFrame L k s (runBlockA s (setCode L Γ g t i v)) := by
  simp only [setCode, runBlockA_append]
  obtain ⟨h1, h2⟩ := compileExpr_correct hL Γ v 0 s hv hR
  obtain ⟨m1, m2⟩ := maskTail_correct hL (Γ t) 0 (runBlockA s (compileExpr L Γ 0 v))
  have f := h2.trans m2
  generalize runBlockA (runBlockA s (compileExpr L Γ 0 v)) (maskCode L (Γ t) 0) = s2 at m1 f
  rw [h1] at m1
  obtain ⟨i1, i2⟩ := compileExpr_correct hL Γ i 1 s2 hi (f.stateRel hR)
  have hv3 := i2.tmp_self
  rw [m1] at hv3
  have f3 := f.trans i2.succ
  generalize runBlockA s2 (compileExpr L Γ 1 i) = s3 at i1 i2 hv3 f3
  have hR3 : StateRel L σ s3 := f3.stateRel hR
  have hgt : ∀ j, g ≠ .tmp j := RegName.not_tmp_of_guardAt hg
  have hg3 : s3.regs (L.name g) = if b then 1 else 0 := (f3.1 g (fun j _ => hgt j)).trans hgv
  generalize hs4 : runBlockA (runBlockA s3 (selCode L t 1)) [.mov (tR L 4) (.imm 0),
     .cmp (L.name g) (.reg (tR L 4)), .cmove (tR L 2) (.reg (L.name .sink)),
     .cmove (tR L 3) (.reg (tR L 4)), .storeMemIdx (tR L 2) (tR L 3) 8 (.reg (tR L 0))] = s4
  set idx := i.eval Γ σ with hidx
  set val := v.eval Γ σ &&& (Γ t).mask with hval
  have hlen := hR3.lenLt t ht
  have e1 : s4.mem = write64 s3.mem
      (if b ∧ idx.toNat < (σ.bufs t).length then cellAddr (s3.regs (L.name (.ptr t))) idx.toNat
       else s3.regs (L.name .sink)) val := by
    subst hs4
    simp only [selCode, runBlockA_cons, runBlockA_nil, evalA_mov, evalA_cmp, evalA_cmovb,
      evalA_cmove, evalA_storeMemIdx]
    simp only [tR, upd, opv, hL.eq_iff, cmpFlags_zf, cmpFlags_cf, hR3.len t ht]
    simp only [tR] at i1 hv3
    by_cases hin : idx.toNat < (σ.bufs t).length
    · have hin' : idx < BitVec.ofNat 64 (σ.bufs t).length := (lt_ofNat_iff _ _ hlen).2 hin
      cases b <;> simp [hgt, hg3, i1, hv3, hin, hin', cellAddr_zero]
    · have hin' : ¬ idx < BitVec.ofNat 64 (σ.bufs t).length := mt (lt_ofNat_iff _ _ hlen).1 hin
      cases b <;> simp [hgt, hg3, i1, hv3, hin, hin', cellAddr_zero]
  have e2 : ∀ n, (∀ j, n ≠ .tmp j) → s4.regs (L.name n) = s3.regs (L.name n) := by
    intro n hn
    subst hs4
    simp only [selCode, runBlockA_cons, runBlockA_nil, evalA_mov, evalA_cmp, evalA_cmovb,
      evalA_cmove, evalA_storeMemIdx]
    simp [tR, upd, hL.eq_iff, hn]
  have fr : ∀ n, n.scratch = false → s4.regs (L.name n) = s3.regs (L.name n) :=
    fun n hn => e2 n (fun j e => by subst e; simp [RegName.scratch] at hn)
  refine ⟨?_, ?_⟩
  · by_cases hin : b ∧ idx.toNat < (σ.bufs t).length
    · obtain ⟨rfl, hin⟩ := hin
      rw [if_pos (by simp [hin])] at e1
      exact hR3.store ht hin val fr e1
    · rw [if_neg hin] at e1
      have h0 := hR3.storeSink val fr e1
      cases b
      · exact h0
      · have hle : (σ.bufs t).length ≤ idx.toNat := by simp at hin; omega
        simp only [if_true, FStmt.exec, ← hidx, ← hval, List.set_eq_of_length_le hle,
          FState.setBuf_self]
        exact h0
  · intro n hn
    rw [e2 n (fun j e => by subst e; simp [RegName.written] at hn)]
    exact f3.1 n (fun j _ e => by subst e; simp [RegName.written] at hn)

theorem iteGuards_spec {L : Layout} (hL : LayoutOK L) {k : Nat} {g : RegName}
    (hg : g.guardAt k = true) (b : Bool) (s : AState)
    (hgv : s.regs (L.name g) = if b then 1 else 0) :
    (runBlockA s (iteGuards L g k)).regs (L.name (.gThen (k + 1))) =
        (if (b && s.regs (tR L 0) != 0) = true then 1 else 0) ∧
      (runBlockA s (iteGuards L g k)).regs (L.name (.gElse (k + 1))) =
        (if (b && s.regs (tR L 0) == 0) = true then 1 else 0) ∧
      (∀ n, (∀ j, n ≠ .tmp j) → n ≠ .gThen (k + 1) → n ≠ .gElse (k + 1) →
        (runBlockA s (iteGuards L g k)).regs (L.name n) = s.regs (L.name n)) ∧
      (runBlockA s (iteGuards L g k)).mem = s.mem := by
  have hgt : ∀ j, g ≠ .tmp j := RegName.not_tmp_of_guardAt hg
  have hg1 : g ≠ .gThen (k + 1) := by rintro rfl; simp [RegName.guardAt] at hg; omega
  have hg2 : g ≠ .gElse (k + 1) := by rintro rfl; simp [RegName.guardAt] at hg; omega
  simp only [iteGuards, runBlockA_cons, runBlockA_nil, evalA_mov, evalA_cmp, evalA_cmove]
  refine ⟨?_, ?_, ?_, by first | rfl | trivial⟩
  · simp only [tR, upd, opv, hL.eq_iff, cmpFlags_zf]
    by_cases hc : s.regs (L.name (.tmp 0)) = 0 <;> cases b <;> simp [hc, hgt, hgv]
  · simp only [tR, upd, opv, hL.eq_iff, cmpFlags_zf]
    by_cases hc : s.regs (L.name (.tmp 0)) = 0 <;> cases b <;> simp [hc, hgt, hg1, hg2, hgv]
  · intro n hn h1 h2
    simp [tR, upd, hL.eq_iff, hn, h1, h2]

theorem armGuards_spec {L : Layout} (hL : LayoutOK L) (k tag : Nat) (rem : Bool) (s : AState)
    (hrem : s.regs (L.name (.gElse (k + 1))) = if rem then 1 else 0) :
    (runBlockA s (armGuards L k tag)).regs (L.name (.gThen (k + 1))) =
        (if (rem && decide (s.regs (L.name (.gTag (k + 1))) = BitVec.ofNat 64 tag)) = true
          then 1 else 0) ∧
      (runBlockA s (armGuards L k tag)).regs (L.name (.gElse (k + 1))) =
        (if (rem && !decide (s.regs (L.name (.gTag (k + 1))) = BitVec.ofNat 64 tag)) = true
          then 1 else 0) ∧
      (∀ n, (∀ j, n ≠ .tmp j) → n ≠ .gThen (k + 1) → n ≠ .gElse (k + 1) →
        (runBlockA s (armGuards L k tag)).regs (L.name n) = s.regs (L.name n)) ∧
      (runBlockA s (armGuards L k tag)).mem = s.mem := by
  simp only [armGuards, runBlockA_cons, runBlockA_nil, evalA_mov, evalA_cmp, evalA_cmove]
  refine ⟨?_, ?_, ?_, by first | rfl | trivial⟩
  · simp only [tR, upd, opv, hL.eq_iff, cmpFlags_zf]
    by_cases hc : s.regs (L.name (.gTag (k + 1))) = BitVec.ofNat 64 tag <;> cases rem <;>
      simp [hc, hrem]
  · simp only [tR, upd, opv, hL.eq_iff, cmpFlags_zf]
    by_cases hc : s.regs (L.name (.gTag (k + 1))) = BitVec.ofNat 64 tag <;> cases rem <;>
      simp [hc, hrem]
  · intro n hn h1 h2
    simp [tR, upd, hL.eq_iff, hn, h1, h2]

theorem matchPrologue_spec {L : Layout} (hL : LayoutOK L) {k : Nat} {g : RegName}
    (hg : g.guardAt k = true) {σ : FState} {s : AState} (hR : StateRel L σ s) {t : String}
    (ht : t ∈ L.spans) :
    (runBlockA s (matchPrologue L g k t)).regs (L.name (.gTag (k + 1))) = (σ.bufs t).getD 0 0 ∧
      (runBlockA s (matchPrologue L g k t)).regs (L.name (.gElse (k + 1))) = s.regs (L.name g) ∧
      (∀ n, (∀ j, n ≠ .tmp j) → n ≠ .gTag (k + 1) → n ≠ .gElse (k + 1) →
        (runBlockA s (matchPrologue L g k t)).regs (L.name n) = s.regs (L.name n)) ∧
      (runBlockA s (matchPrologue L g k t)).mem = s.mem := by
  have hgt : ∀ j, g ≠ .tmp j := RegName.not_tmp_of_guardAt hg
  have hg1 : g ≠ .gTag (k + 1) := by rintro rfl; simp [RegName.guardAt] at hg
  simp only [matchPrologue, List.cons_append, runBlockA_cons, runBlockA_append]
  obtain ⟨a1, a2⟩ := movTmp_post hL 0 s (.imm 0)
  obtain ⟨c1, c2⟩ := getCode_correct hL (a2.stateRel hR) ht 0
  have f := a2.trans c2
  rw [a1] at c1
  generalize runBlockA (evalInstrA s (.mov (tR L 0) (.imm 0))) (getCode L t 0) = s2 at c1 f
  have hg2 : s2.regs (L.name g) = s.regs (L.name g) := f.1 g (fun j _ => hgt j)
  simp only [runBlockA_nil, evalA_mov]
  refine ⟨?_, ?_, ?_, f.2⟩
  · simp only [tR, opv] at c1 ⊢
    simp [upd, hL.eq_iff, c1]
  · simp [upd, opv, hL.eq_iff, hg2, hg1]
  · intro n hn h1 h2
    simp only [upd, opv, hL.eq_iff, h1, h2, if_false]
    exact f.1 n (fun j _ => hn j)

theorem RegName.ne_of_written {k : Nat} {n : RegName} (hn : n.written k = false) :
    (∀ j, n ≠ .tmp j) ∧ n ≠ .gThen (k + 1) ∧ n ≠ .gElse (k + 1) ∧ n ≠ .gTag (k + 1) := by
  refine ⟨fun j e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> subst e <;>
    simp [RegName.written] at hn

theorem RegName.ne_of_scratch {n : RegName} (hn : n.scratch = false) :
    (∀ j, n ≠ .tmp j) ∧ (∀ j, n ≠ .gThen j) ∧ (∀ j, n ≠ .gElse j) ∧ (∀ j, n ≠ .gTag j) := by
  refine ⟨fun j e => ?_, fun j e => ?_, fun j e => ?_, fun j e => ?_⟩ <;> subst e <;>
    simp [RegName.scratch] at hn

theorem eq_ofNat_iff (w : BitVec 64) (n : Nat) (hn : n < 2 ^ 64) :
    w = BitVec.ofNat 64 n ↔ n = w.toNat := by
  constructor
  · rintro rfl; simp [Nat.mod_eq_of_lt hn]
  · rintro rfl; simp

mutual

/-- **Statement compiler correctness.** For a statement in scope, compiled at depth `k`
under a guard register of depth at most `k` holding `1` or `0` as `b` is true or false,
the code relates the state after the statement when `b` holds and the state before it
otherwise, and changes no named register outside the temporaries, the scalar registers
and the guard registers of depths above `k`. -/
theorem compileStmt_correct {L : Layout} (hL : LayoutOK L) (Γ : String → FWidth) :
    ∀ (st : FStmt) (k : Nat) (g : RegName) (σ : FState) (s : AState) (b : Bool),
      st.fits L = true → g.guardAt k = true → s.regs (L.name g) = (if b then 1 else 0) →
      StateRel L σ s →
      StateRel L (if b then st.exec Γ σ else σ) (runBlockA s (compileStmt L Γ k g st)) ∧
        StmtFrame L k s (runBlockA s (compileStmt L Γ k g st))
  | .skip, _, _, σ, s, b, _, _, _, hR => by
      simp only [compileStmt, runBlockA_nil, FStmt.exec, ite_self]
      exact ⟨hR, fun _ _ => rfl⟩
  | .seq a c, k, g, σ, s, b, hf, hg, hgv, hR => by
      simp only [FStmt.fits, Bool.and_eq_true] at hf
      simp only [compileStmt, runBlockA_append]
      obtain ⟨r1, f1⟩ := compileStmt_correct hL Γ a k g σ s b hf.1 hg hgv hR
      have hgv1 := (f1 g (RegName.written_of_guardAt hg)).trans hgv
      obtain ⟨r2, f2⟩ := compileStmt_correct hL Γ c k g _ _ b hf.2 hg hgv1 r1
      refine ⟨?_, f1.trans f2⟩
      cases b <;> simpa [FStmt.exec] using r2
  | .assign x e, k, g, σ, s, b, hf, hg, hgv, hR => by
      simp only [FStmt.fits] at hf
      simp only [compileStmt]
      exact assignCode_correct hL Γ hg b hgv hf hR
  | .spanSet t i v, k, g, σ, s, b, hf, hg, hgv, hR => by
      simp only [FStmt.fits, Bool.and_eq_true, decide_eq_true_eq] at hf
      simp only [compileStmt]
      exact setCode_correct hL Γ hg b hgv hf.1.1 hf.1.2 hf.2 hR
  | .ite c a e, k, g, σ, s, b, hf, hg, hgv, hR => by
      simp only [FStmt.fits, Bool.and_eq_true] at hf
      simp only [compileStmt, runBlockA_append]
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
      obtain ⟨r3, f3⟩ := compileStmt_correct hL Γ a (k + 1) (.gThen (k + 1)) σ s2 _ hf.1.2
        (by simp [RegName.guardAt]) g1 hR2
      have ge3 := (f3 (.gElse (k + 1)) (by simp [RegName.written])).trans g2
      obtain ⟨r4, f4⟩ := compileStmt_correct hL Γ e (k + 1) (.gElse (k + 1)) _ _ _ hf.2
        (by simp [RegName.guardAt]) ge3 r3
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
  | .matchTag t arms dflt, k, g, σ, s, b, hf, hg, hgv, hR => by
      simp only [FStmt.fits, Bool.and_eq_true, decide_eq_true_eq] at hf
      simp only [compileStmt, runBlockA_append]
      obtain ⟨p1, p2, p3, p4⟩ := matchPrologue_spec hL hg hR hf.1.1
      rw [hgv] at p2
      generalize runBlockA s (matchPrologue L g k t) = s1 at p1 p2 p3 p4
      have hR1 : StateRel L σ s1 := hR.frame (fun n hn => by
        obtain ⟨h1, -, h3, h4⟩ := RegName.ne_of_scratch hn
        exact p3 n h1 (h4 _) (h3 _)) p4
      have f1 : StmtFrame L k s s1 := fun n hn => by
        obtain ⟨h1, -, h3, h4⟩ := RegName.ne_of_written hn
        exact p3 n h1 h4 h3
      obtain ⟨a1, a2, -, a4⟩ := compileArms_correct hL Γ arms k σ s1 b _ hf.1.2 p1 p2 hR1
      obtain ⟨d1, d2⟩ := compileStmt_correct hL Γ dflt (k + 1) (.gElse (k + 1)) _ _ _ hf.2
        (by simp [RegName.guardAt]) a2 a1
      refine ⟨?_, f1.trans (a4.trans d2.succ)⟩
      cases b
      · simpa using d1
      · simp only [FStmt.exec, if_true, Bool.true_and] at d1 ⊢
        rcases hx : FStmt.execArms Γ ((σ.bufs t).getD 0 0).toNat arms σ with _ | σ' <;>
          simp only [hx, Option.isNone_none, Option.isNone_some, Option.getD_none,
            Option.getD_some, if_true, if_false, Bool.false_eq_true] at d1 ⊢ <;> exact d1
  | .forLit .., _, _, _, _, _, hf, _, _, _ => by simp [FStmt.fits] at hf
  | .forLen .., _, _, _, _, _, hf, _, _, _ => by simp [FStmt.fits] at hf

/-- **Arm compiler correctness.** With the tag word `w` in `gTag (k + 1)` and the
not-yet-matched flag `rem` in `gElse (k + 1)`, the arms' code relates the state after the
first arm whose tag is `w.toNat` when `rem` holds and such an arm exists, and the state
before it otherwise; the flag register ends holding whether `rem` held and no arm
matched. -/
theorem compileArms_correct {L : Layout} (hL : LayoutOK L) (Γ : String → FWidth) :
    ∀ (arms : List (Nat × FStmt)) (k : Nat) (σ : FState) (s : AState) (rem : Bool)
      (w : BitVec 64), FStmt.fitsArms L arms = true →
      s.regs (L.name (.gTag (k + 1))) = w →
      s.regs (L.name (.gElse (k + 1))) = (if rem then 1 else 0) → StateRel L σ s →
      StateRel L (if rem then (FStmt.execArms Γ w.toNat arms σ).getD σ else σ)
          (runBlockA s (compileArms L Γ k arms)) ∧
        (runBlockA s (compileArms L Γ k arms)).regs (L.name (.gElse (k + 1))) =
          (if (rem && (FStmt.execArms Γ w.toNat arms σ).isNone) = true then 1 else 0) ∧
        (runBlockA s (compileArms L Γ k arms)).regs (L.name (.gTag (k + 1))) = w ∧
        StmtFrame L k s (runBlockA s (compileArms L Γ k arms))
  | [], _, σ, s, rem, _, _, hw, hr, hR => by
      simp only [compileArms, runBlockA_nil, FStmt.execArms, Option.getD_none, ite_self,
        Option.isNone_none, Bool.and_true]
      exact ⟨hR, hr, hw, fun _ _ => rfl⟩
  | (tag, body) :: rest, k, σ, s, rem, w, hf, hw, hr, hR => by
      simp only [FStmt.fitsArms, Bool.and_eq_true, decide_eq_true_eq] at hf
      simp only [compileArms, runBlockA_append]
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
      obtain ⟨r2, f2⟩ := compileStmt_correct hL Γ body (k + 1) (.gThen (k + 1)) σ s1 _ hf.1.2
        (by simp [RegName.guardAt]) g1 hR1
      have ge2 := (f2 (.gElse (k + 1)) (by simp [RegName.written])).trans g2
      have gt2 := (f2 (.gTag (k + 1)) (by simp [RegName.written])).trans hw1
      obtain ⟨a1, a2, a3, a4⟩ := compileArms_correct hL Γ rest k _ _ _ w hf.2 gt2 ge2 r2
      refine ⟨?_, ?_, a3, f1.trans (f2.succ.trans a4)⟩
      · generalize runBlockA (runBlockA s1 (compileStmt L Γ (k + 1) (.gThen (k + 1)) body))
          (compileArms L Γ k rest) = sF at a1 ⊢
        cases rem <;> by_cases hk : tag = w.toNat <;>
          simp [FStmt.execArms, hk] at a1 ⊢ <;> exact a1
      · rw [a2]
        cases rem <;> by_cases hk : tag = w.toNat <;> simp [FStmt.execArms, hk]

end

/-- **Program compiler correctness.** For a program in scope and a machine state related
to the source state by `StateRel`, temporary 0 is nonzero after the compiled program
exactly when the program answers `true`. -/
theorem compileProg_correct {L : Layout} (hL : LayoutOK L) (p : FProg) (hf : p.fits L = true)
    {σ : FState} {s : AState} (hR : StateRel L σ s) :
    (runBlockA s (compileProg L p)).regs (tR L 0) ≠ 0 ↔ p.run σ = true := by
  simp only [FProg.fits, Bool.and_eq_true] at hf
  simp only [compileProg, List.cons_append, runBlockA_cons, runBlockA_append]
  have hR0 : StateRel L σ (evalInstrA s (.mov (L.name (.gThen 0)) (.imm 1))) := by
    refine hR.frame (fun n hn => ?_) (by rw [evalA_mov])
    obtain ⟨-, h2, -, -⟩ := RegName.ne_of_scratch hn
    rw [evalA_mov]
    simp [upd, hL.eq_iff, h2 0]
  have hg0 : (evalInstrA s (.mov (L.name (.gThen 0)) (.imm 1))).regs (L.name (.gThen 0)) =
      if true = true then 1 else 0 := by
    rw [evalA_mov]; simp [upd, opv]
  obtain ⟨r1, -⟩ := compileStmt_correct hL p.widths p.body 0 (.gThen 0) σ _ true hf.1
    (by simp [RegName.guardAt]) hg0 hR0
  simp only [if_true] at r1
  obtain ⟨e1, -⟩ := compileExpr_correct hL p.widths p.result 0 _ hf.2 r1
  rw [e1]
  simp [FProg.run]

end VerifiedEval

end
