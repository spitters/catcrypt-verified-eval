/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.FragmentCompile
public import CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeJBlock6Roundtrip
public import CatCrypt.Crypto.SecureCompilation.X86Backend.EncodedBlockCorres

/-!
# The compiled fragment through the byte encoder and decoder

The fragment compiler `compileProg` of
`VerifiedEval.FragmentCompile` emits straight-line
`JInstr 64` code over block-level register names. The shipped encoder `encodeJBlock6`
resolves each name through a register allocation `alloc`, and the decoder
`decodeJStream6` of `CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeJBlock6Roundtrip`
reads the bytes back as the block with every name resolved (`renameJ alloc`). This module
proves that every instruction the compiler emits is in the decoder's covered set, so the
bytes decode back, and that running the decoded block on a state whose physical registers
hold the values of the block-level registers computes the same result as the compiled
block on the address-memory machine `runBlockA`.

## Scope

The coverage needs two conditions besides `FProg.fits`. `AllocOK L alloc` states that no
temporary register is allocated to `%rsp`: temporaries are the index registers of the
compiled `loadMemIdx`/`storeMemIdx`, and a SIB byte cannot name `%rsp` as an index.
`FProg.litsFit` states that every literal of the program is below `2 ^ 64`, the range of
the `mov` immediate the decoder inverts. The renaming theorem needs the resolution
`nameOf alloc` to be injective on the register names the compiled block mentions
(`RenInjOn`); this is a condition on the program as well as on the allocation, since a
layout names infinitely many roles and an allocation has sixteen registers.

## Main definitions

* `FExpr.litsFit`, `FStmt.litsFit`, `FProg.litsFit`: every literal is below `2 ^ 64`.
* `AllocOK`: the allocation conditions of the coverage.
* `fragOK`: an instruction is in `blockCovered6` and satisfies `mulxRdxOk`.
* `ARelOn`: the address-state relation of a register renaming on a list of names.

## Main results

* `compileProg_covered`, `compileProg_mulxRdxOk`: every instruction of `compileProg L p`
  is in `blockCovered6 alloc` and satisfies `mulxRdxOk alloc`.
* `compileProg_roundtrip`: the `encodeJBlock6` bytes of `compileProg L p` decode to
  `(compileProg L p).map (renameJ alloc)`.
* `evalInstrA_renameInstr_rel_on`, `runBlockA_renameBlock_rel_on`: a renaming injective on
  the names a block mentions commutes with `runBlockA`: registers correspond through the
  renaming, and flags and memory are equal.
* `compileProg_bytes_correct`: the block decoded from the shipped bytes, run on a physical
  state related to a state `StateRel`-related to `σ`, leaves a nonzero value in the
  physical register of temporary 0 exactly when `p.run σ = true`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc regOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (encodeJInstr6 encodeJBlock6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.EncodedBlockCorres
  (loadSymFree map_renameJ_eq_renameBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeJBlock6Roundtrip
open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc (renameInstr renameOperand renameBlock)
open CatCrypt.Crypto.Optimizer.GenericRegAlloc (RenInjOn)
open CatCrypt.Crypto.Optimizer.JInstrRegAllocValidated (bNamesX)
open CatCrypt.Crypto.Optimizer.JInstrRegAllocScoped

/-! ## Literal scope -/

/-- Every literal of the expression is below `2 ^ 64`. -/
def FExpr.litsFit : FExpr → Bool
  | .var _ => true
  | .lit n => decide (n < 2 ^ 64)
  | .bin _ a b => a.litsFit && b.litsFit
  | .not a => a.litsFit
  | .spanLen _ => true
  | .spanGet _ i => i.litsFit
  | .tagOf _ => true
  | .payload _ => true

mutual

/-- Every literal of every expression of the statement is below `2 ^ 64`. -/
def FStmt.litsFit : FStmt → Bool
  | .skip => true
  | .seq a b => a.litsFit && b.litsFit
  | .assign _ e => e.litsFit
  | .spanSet _ i v => i.litsFit && v.litsFit
  | .ite c a b => c.litsFit && a.litsFit && b.litsFit
  | .matchTag _ arms dflt => FStmt.litsFitArms arms && dflt.litsFit
  | .forLit _ _ body => body.litsFit
  | .forLen _ _ body => body.litsFit

/-- Every literal of every arm is below `2 ^ 64`. -/
def FStmt.litsFitArms : List (Nat × FStmt) → Bool
  | [] => true
  | (_, b) :: rest => b.litsFit && FStmt.litsFitArms rest

end

/-- Every literal of the program's body and result is below `2 ^ 64`. -/
def FProg.litsFit (p : FProg) : Bool := p.body.litsFit && p.result.litsFit

/-! ## Coverage -/

/-- The allocation conditions under which the compiled code is in the round-trip set:
every temporary register, which the compiled indexed loads and stores use as their index
register, is allocated to a register other than `%rsp`. -/
structure AllocOK (L : Layout) (alloc : GpAlloc) : Prop where
  /-- No temporary is allocated to `%rsp`, register number `4`. -/
  tmp_ne_rsp : ∀ k, gpNum (regOf alloc (L.name (.tmp k))) ≠ 4

/-- The instruction is in the round-trip set `blockCovered6 alloc` and satisfies
`mulxRdxOk alloc`. -/
def fragOK (alloc : GpAlloc) (i : JInstr 64) : Bool :=
  blockCovered6 alloc i && mulxRdxOk alloc i

section Instr

variable (alloc : GpAlloc)

theorem fragOK_mov_reg (d r : String) : fragOK alloc (.mov d (.reg r)) = true := rfl

theorem fragOK_mov_imm (d : String) (v : Nat) (hv : v < 2 ^ 64) :
    fragOK alloc (.mov d (.imm v)) = true := by
  simp only [fragOK, blockCovered6, blockCovered, decodableJ, mulxRdxOk, Bool.and_true,
    Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inl hv

theorem fragOK_cmp_reg (a r : String) : fragOK alloc (.cmp a (.reg r)) = true := by
  simp [fragOK, blockCovered6, blockCovered, decodableJ, newCovered6, mulxRdxOk]

theorem fragOK_cmove (d r : String) : fragOK alloc (.cmove d (.reg r)) = true := rfl

theorem fragOK_cmovne (d r : String) : fragOK alloc (.cmovne d (.reg r)) = true := rfl

theorem fragOK_cmovb (d r : String) : fragOK alloc (.cmovb d (.reg r)) = true := rfl

theorem fragOK_and (d r : String) : fragOK alloc (.and_ d (.reg r)) = true := rfl

theorem fragOK_loadMemIdx (d b x : String) (hx : gpNum (regOf alloc x) ≠ 4) :
    fragOK alloc (.loadMemIdx d b x 8) = true := by
  simp [fragOK, blockCovered6, blockCovered, decodableJ, newCovered6, mulxRdxOk, scaleOk, hx]

theorem fragOK_storeMemIdx (b x r : String) (hx : gpNum (regOf alloc x) ≠ 4) :
    fragOK alloc (.storeMemIdx b x 8 (.reg r)) = true := by
  simp [fragOK, blockCovered6, blockCovered, decodableJ, newCovered6, mulxRdxOk, scaleOk, hx]

theorem fragOK_arith_reg (op : FBinop) (hs : op.isShift = false) (d r : String) :
    fragOK alloc (arithInstr op d (.reg r)) = true := by
  cases op <;> first | rfl | simp [FBinop.isShift] at hs

theorem fragOK_shift_imm (op : FBinop) (hs : op.isShift = true) (d : String) (n : Nat)
    (hn : n < 64) : fragOK alloc (arithInstr op d (.imm n)) = true := by
  cases op <;> simp [FBinop.isShift] at hs <;>
    simp [arithInstr, fragOK, blockCovered6, blockCovered, decodableJ, mulxRdxOk] <;> omega

end Instr

theorem FWidth.mask_lt (w : FWidth) : 2 ^ w.bits - 1 < 2 ^ 64 := by
  cases w <;> decide

variable {L : Layout} {alloc : GpAlloc}

theorem maskCode_fragOK (w : FWidth) (d : Nat) :
    ∀ i ∈ maskCode L w d, fragOK alloc i = true := by
  simp only [maskCode, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  exact ⟨fragOK_mov_imm _ _ _ (FWidth.mask_lt w), fragOK_and _ _ _⟩

theorem selCode_fragOK (t : String) (d : Nat) :
    ∀ i ∈ selCode L t d, fragOK alloc i = true := by
  simp only [selCode, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  exact ⟨fragOK_mov_reg _ _ _, fragOK_mov_imm _ _ _ (by decide), fragOK_cmp_reg _ _ _,
    fragOK_cmovb _ _ _, fragOK_cmovb _ _ _⟩

theorem getCode_fragOK (hA : AllocOK L alloc) (t : String) (d : Nat) :
    ∀ i ∈ getCode L t d, fragOK alloc i = true := by
  simp only [getCode, List.forall_mem_append]
  refine ⟨selCode_fragOK t d, ?_⟩
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨fragOK_loadMemIdx _ _ _ _ (hA.tmp_ne_rsp (d + 2)), fragOK_mov_imm _ _ _ (by decide),
    fragOK_cmovb _ _ _⟩

theorem cmpCode_fragOK (op : FBinop) (d : Nat) :
    ∀ i ∈ cmpCode L op d, fragOK alloc i = true := by
  cases op <;>
    simp only [cmpCode, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
      and_true] <;>
    trivial

theorem notCode_fragOK (d : Nat) : ∀ i ∈ notCode L d, fragOK alloc i = true := by
  simp only [notCode, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  exact ⟨fragOK_mov_imm _ _ _ (by decide), fragOK_cmp_reg _ _ _,
    fragOK_mov_imm _ _ _ (by decide), fragOK_mov_imm _ _ _ (by decide), fragOK_cmove _ _ _⟩

/-- Every instruction of the code of an expression in scope is in the round-trip set. -/
theorem compileExpr_fragOK (hA : AllocOK L alloc) (Γ : String → FWidth) :
    ∀ (e : FExpr) (d : Nat), e.fits L = true → e.litsFit = true →
      ∀ i ∈ compileExpr L Γ d e, fragOK alloc i = true
  | .var x, d, _, _ => by simp [compileExpr, fragOK_mov_reg]
  | .lit n, d, _, hl => by
      simp only [FExpr.litsFit, decide_eq_true_eq] at hl
      simp [compileExpr, fragOK_mov_imm _ _ _ hl]
  | .spanLen t, d, _, _ => by simp [compileExpr, fragOK_mov_reg]
  | .bin op a b, d, hf, hl => by
      simp only [FExpr.litsFit, Bool.and_eq_true] at hl
      by_cases hc : op.isCompare = true
      · have hs := FBinop.isShift_of_isCompare hc
        simp only [FExpr.fits, hs, Bool.false_eq_true, ite_false, Bool.and_eq_true] at hf
        simp only [compileExpr, hc, ite_true, List.forall_mem_append]
        exact ⟨⟨compileExpr_fragOK hA Γ a d hf.1 hl.1,
          compileExpr_fragOK hA Γ b (d + 1) hf.2 hl.2⟩, cmpCode_fragOK op d⟩
      · simp only [Bool.not_eq_true] at hc
        by_cases hs : op.isShift = true
        · cases b with
          | lit n =>
            simp only [FExpr.fits, hs, ite_true, Bool.and_eq_true, decide_eq_true_eq] at hf
            simp only [compileExpr, hc, hs, Bool.false_eq_true, ite_false, ite_true,
              List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
              implies_true, and_true]
            exact ⟨⟨compileExpr_fragOK hA Γ a d hf.2 hl.1,
              fragOK_shift_imm alloc op hs _ n hf.1⟩, maskCode_fragOK _ d⟩
          | _ => simp [FExpr.fits, hs] at hf
        · simp only [Bool.not_eq_true] at hs
          simp only [FExpr.fits, hs, Bool.false_eq_true, ite_false, Bool.and_eq_true] at hf
          simp only [compileExpr, hc, hs, Bool.false_eq_true, ite_false,
            List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
            implies_true, and_true]
          exact ⟨⟨⟨compileExpr_fragOK hA Γ a d hf.1 hl.1,
            compileExpr_fragOK hA Γ b (d + 1) hf.2 hl.2⟩, fragOK_arith_reg alloc op hs _ _⟩,
            maskCode_fragOK _ d⟩
  | .not a, d, hf, hl => by
      simp only [FExpr.fits] at hf
      simp only [FExpr.litsFit] at hl
      simp only [compileExpr, List.forall_mem_append]
      exact ⟨compileExpr_fragOK hA Γ a d hf hl, notCode_fragOK d⟩
  | .spanGet t i, d, hf, hl => by
      simp only [FExpr.fits, Bool.and_eq_true] at hf
      simp only [FExpr.litsFit] at hl
      simp only [compileExpr, List.forall_mem_append]
      exact ⟨compileExpr_fragOK hA Γ i d hf.2 hl, getCode_fragOK hA t d⟩
  | .tagOf t, d, _, _ => by
      simp only [compileExpr, List.forall_mem_cons]
      exact ⟨fragOK_mov_imm _ _ _ (by decide), getCode_fragOK hA t d⟩
  | .payload t, d, _, _ => by
      simp only [compileExpr, List.forall_mem_cons]
      exact ⟨fragOK_mov_imm _ _ _ (by decide), getCode_fragOK hA t d⟩

theorem assignCode_fragOK (hA : AllocOK L alloc) (Γ : String → FWidth) (g : RegName)
    (x : String) (e : FExpr) (hf : e.fits L = true) (hl : e.litsFit = true) :
    ∀ i ∈ assignCode L Γ g x e, fragOK alloc i = true := by
  simp only [assignCode, List.forall_mem_append]
  refine ⟨⟨compileExpr_fragOK hA Γ e 0 hf hl, maskCode_fragOK _ 0⟩, ?_⟩
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨fragOK_mov_imm _ _ _ (by decide), fragOK_cmp_reg _ _ _, fragOK_cmovne _ _ _⟩

theorem setCode_fragOK (hA : AllocOK L alloc) (Γ : String → FWidth) (g : RegName)
    (t : String) (i v : FExpr) (hi : i.fits L = true) (hv : v.fits L = true)
    (hli : i.litsFit = true) (hlv : v.litsFit = true) :
    ∀ j ∈ setCode L Γ g t i v, fragOK alloc j = true := by
  simp only [setCode, List.forall_mem_append]
  refine ⟨⟨⟨⟨compileExpr_fragOK hA Γ v 0 hv hlv, maskCode_fragOK _ 0⟩,
    compileExpr_fragOK hA Γ i 1 hi hli⟩, selCode_fragOK t 1⟩, ?_⟩
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨fragOK_mov_imm _ _ _ (by decide), fragOK_cmp_reg _ _ _, fragOK_cmove _ _ _,
    fragOK_cmove _ _ _, fragOK_storeMemIdx _ _ _ _ (hA.tmp_ne_rsp 3)⟩

theorem iteGuards_fragOK (g : RegName) (k : Nat) :
    ∀ i ∈ iteGuards L g k, fragOK alloc i = true := by
  simp only [iteGuards, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  exact ⟨fragOK_mov_imm _ _ _ (by decide), fragOK_cmp_reg _ _ _, fragOK_mov_reg _ _ _,
    fragOK_cmove _ _ _, fragOK_mov_imm _ _ _ (by decide), fragOK_cmove _ _ _⟩

theorem armGuards_fragOK (k tag : Nat) (ht : tag < 2 ^ 64) :
    ∀ i ∈ armGuards L k tag, fragOK alloc i = true := by
  simp only [armGuards, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  exact ⟨fragOK_mov_imm _ _ _ ht, fragOK_cmp_reg _ _ _, fragOK_mov_imm _ _ _ (by decide),
    fragOK_mov_imm _ _ _ (by decide), fragOK_cmove _ _ _, fragOK_cmove _ _ _⟩

theorem matchPrologue_fragOK (hA : AllocOK L alloc) (g : RegName) (k : Nat) (t : String) :
    ∀ i ∈ matchPrologue L g k t, fragOK alloc i = true := by
  simp only [matchPrologue, List.forall_mem_append, List.forall_mem_cons]
  refine ⟨⟨fragOK_mov_imm _ _ _ (by decide), getCode_fragOK hA t 0⟩, ?_⟩
  simp only [List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨fragOK_mov_reg _ _ _, fragOK_mov_reg _ _ _⟩

mutual

/-- Every instruction of the code of a statement in scope is in the round-trip set. -/
theorem compileStmt_fragOK (hA : AllocOK L alloc) (Γ : String → FWidth) :
    ∀ (st : FStmt) (k : Nat) (g : RegName), st.fits L = true → st.litsFit = true →
      ∀ i ∈ compileStmt L Γ k g st, fragOK alloc i = true
  | .skip, _, _, _, _ => by simp [compileStmt]
  | .seq a c, k, g, hf, hl => by
      simp only [FStmt.fits, Bool.and_eq_true] at hf
      simp only [FStmt.litsFit, Bool.and_eq_true] at hl
      simp only [compileStmt, List.forall_mem_append]
      exact ⟨compileStmt_fragOK hA Γ a k g hf.1 hl.1, compileStmt_fragOK hA Γ c k g hf.2 hl.2⟩
  | .assign x e, _, g, hf, hl => by
      simp only [FStmt.fits] at hf
      simp only [FStmt.litsFit] at hl
      simp only [compileStmt]
      exact assignCode_fragOK hA Γ g x e hf hl
  | .spanSet t i v, _, g, hf, hl => by
      simp only [FStmt.fits, Bool.and_eq_true] at hf
      simp only [FStmt.litsFit, Bool.and_eq_true] at hl
      simp only [compileStmt]
      exact setCode_fragOK hA Γ g t i v hf.1.2 hf.2 hl.1 hl.2
  | .ite c a e, k, g, hf, hl => by
      simp only [FStmt.fits, Bool.and_eq_true] at hf
      simp only [FStmt.litsFit, Bool.and_eq_true] at hl
      simp only [compileStmt, List.forall_mem_append]
      exact ⟨⟨⟨compileExpr_fragOK hA Γ c 0 hf.1.1 hl.1.1, iteGuards_fragOK g k⟩,
        compileStmt_fragOK hA Γ a (k + 1) _ hf.1.2 hl.1.2⟩,
        compileStmt_fragOK hA Γ e (k + 1) _ hf.2 hl.2⟩
  | .matchTag t arms dflt, k, g, hf, hl => by
      simp only [FStmt.fits, Bool.and_eq_true] at hf
      simp only [FStmt.litsFit, Bool.and_eq_true] at hl
      simp only [compileStmt, List.forall_mem_append]
      exact ⟨⟨matchPrologue_fragOK hA g k t, compileArms_fragOK hA Γ arms k hf.1.2 hl.1⟩,
        compileStmt_fragOK hA Γ dflt (k + 1) _ hf.2 hl.2⟩
  | .forLit .., _, _, hf, _ => by simp [FStmt.fits] at hf
  | .forLen .., _, _, hf, _ => by simp [FStmt.fits] at hf

/-- Every instruction of the code of the arms of a `matchTag` in scope is in the
round-trip set. -/
theorem compileArms_fragOK (hA : AllocOK L alloc) (Γ : String → FWidth) :
    ∀ (arms : List (Nat × FStmt)) (k : Nat), FStmt.fitsArms L arms = true →
      FStmt.litsFitArms arms = true → ∀ i ∈ compileArms L Γ k arms, fragOK alloc i = true
  | [], _, _, _ => by simp [compileArms]
  | (tag, b) :: rest, k, hf, hl => by
      simp only [FStmt.fitsArms, Bool.and_eq_true, decide_eq_true_eq] at hf
      simp only [FStmt.litsFitArms, Bool.and_eq_true] at hl
      simp only [compileArms, List.forall_mem_append]
      exact ⟨⟨armGuards_fragOK k tag hf.1.1, compileStmt_fragOK hA Γ b (k + 1) _ hf.1.2 hl.1⟩,
        compileArms_fragOK hA Γ rest k hf.2 hl.2⟩

end

/-- Every instruction of a compiled program in scope is in the round-trip set. -/
theorem compileProg_fragOK (hA : AllocOK L alloc) (p : FProg) (hf : p.fits L = true)
    (hl : p.litsFit = true) : ∀ i ∈ compileProg L p, fragOK alloc i = true := by
  simp only [FProg.fits, Bool.and_eq_true] at hf
  simp only [FProg.litsFit, Bool.and_eq_true] at hl
  simp only [compileProg, List.cons_append, List.forall_mem_cons, List.forall_mem_append]
  exact ⟨fragOK_mov_imm _ _ _ (by decide),
    compileStmt_fragOK hA p.widths p.body 0 _ hf.1 hl.1,
    compileExpr_fragOK hA p.widths p.result 0 hf.2 hl.2⟩

/-- **Coverage.** Every instruction of a compiled program in scope is in the round-trip
set `blockCovered6 alloc`. -/
theorem compileProg_covered (hA : AllocOK L alloc) (p : FProg) (hf : p.fits L = true)
    (hl : p.litsFit = true) : ∀ i ∈ compileProg L p, blockCovered6 alloc i = true :=
  fun i hi => by
    have h := compileProg_fragOK hA p hf hl i hi
    simp only [fragOK, Bool.and_eq_true] at h
    exact h.1

/-- Every instruction of a compiled program in scope satisfies `mulxRdxOk alloc`. -/
theorem compileProg_mulxRdxOk (hA : AllocOK L alloc) (p : FProg) (hf : p.fits L = true)
    (hl : p.litsFit = true) : ∀ i ∈ compileProg L p, mulxRdxOk alloc i = true :=
  fun i hi => by
    have h := compileProg_fragOK hA p hf hl i hi
    simp only [fragOK, Bool.and_eq_true] at h
    exact h.2

/-- **Byte round trip.** The shipped `encodeJBlock6` bytes of a compiled program in scope
decode, instruction by instruction, to the compiled block with every register name
resolved through the allocation. -/
theorem compileProg_roundtrip (hA : AllocOK L alloc) (p : FProg) (hf : p.fits L = true)
    (hl : p.litsFit = true) :
    decodeJStream6 (compileProg L p).length (encodeJBlock6 alloc (compileProg L p)) =
      some ((compileProg L p).map (renameJ alloc)) :=
  roundtrip_block6 alloc _ (compileProg_covered hA p hf hl) (compileProg_mulxRdxOk hA p hf hl)

/-! ## Renaming on the address-memory machine -/

/-- The address-state relation of a register renaming `ρ` on the names `ns`: register
`ρ n` of `t` holds the value of register `n` of `s` for every `n ∈ ns`, and the flags and
the byte memory are equal. -/
structure ARelOn (ns : List String) (ρ : String → String) (t s : AState) : Prop where
  /-- Registers correspond through the renaming on `ns`. -/
  regsOn : ∀ n ∈ ns, t.regs (ρ n) = s.regs n
  /-- The flags are equal. -/
  flags : t.flags = s.flags
  /-- The byte memories are equal. -/
  mem : t.mem = s.mem

/-- The name-keyed views of `ARelOn`-related address states are `StateRelOn`-related:
bank `ρ b` of the renamed view is read at the same address as bank `b`. -/
theorem ARelOn.view {ns : List String} {ρ : String → String} {t s : AState}
    (h : ARelOn ns ρ t s) : StateRelOn ns ρ t.view s.view where
  regsOn := h.regsOn
  flags := h.flags
  memOn b hb o := by simp only [AState.view, h.regsOn b hb, h.mem]

/-- **One-step renaming.** For `ρ` injective on `ns` and every name of `i` in `ns`, the
renamed instruction on the renamed state and the instruction on the source state give
`ARelOn`-related states. -/
theorem evalInstrA_renameInstr_rel_on {ns : List String} {ρ : String → String}
    (hinj : RenInjOn ns ρ) {t s : AState} (h : ARelOn ns ρ t s) (i : JInstr 64)
    (hsub : ∀ n ∈ bNamesXsym i, n ∈ ns) :
    ARelOn ns ρ (evalInstrA t (renameInstr ρ i)) (evalInstrA s i) := by
  have hv := evalInstr_renameInstr_rel_on hinj h.view i hsub
  refine ⟨hv.regsOn, hv.flags, ?_⟩
  have hr : ∀ n ∈ CatCrypt.Crypto.Optimizer.SpillingRegAlloc.readNames i, n ∈ ns :=
    fun n hn => hsub n (mem_bNamesXsym_of_bNamesX i (by simp [bNamesX, hn]))
  cases i <;> simp only [evalInstrA, renameInstr, writeAddr, h.mem]
  case storeMem b o src =>
    have hb : b ∈ ns := hr b (by simp [CatCrypt.Crypto.Optimizer.SpillingRegAlloc.readNames])
    simp only [writeVal, h.regsOn b hb, renameOperand_eval_on h.view src (fun n hn =>
      hr n (by simp [CatCrypt.Crypto.Optimizer.SpillingRegAlloc.readNames, hn]))]
  case storeMemIdx b x sc src =>
    have hb : b ∈ ns := hr b (by simp [CatCrypt.Crypto.Optimizer.SpillingRegAlloc.readNames])
    have hx : x ∈ ns := hr x (by simp [CatCrypt.Crypto.Optimizer.SpillingRegAlloc.readNames])
    simp only [writeVal, h.regsOn b hb, h.regsOn x hx, renameOperand_eval_on h.view src
      (fun n hn => hr n (by simp [CatCrypt.Crypto.Optimizer.SpillingRegAlloc.readNames, hn]))]
  case addToMem b o src =>
    have hb : b ∈ ns := hr b (by simp [CatCrypt.Crypto.Optimizer.SpillingRegAlloc.readNames])
    simp only [writeVal, JState.load, h.regsOn b hb, h.view.memOn b hb o,
      renameOperand_eval_on h.view src (fun n hn =>
        hr n (by simp [CatCrypt.Crypto.Optimizer.SpillingRegAlloc.readNames, hn]))]

/-- **Block renaming.** For `ρ` injective on `ns` and every name the block mentions in
`ns`, running the renamed block on the renamed state and the block on the source state
give `ARelOn`-related states. -/
theorem runBlockA_renameBlock_rel_on {ns : List String} {ρ : String → String}
    (hinj : RenInjOn ns ρ) (block : List (JInstr 64))
    (hsub : ∀ n ∈ blockNamesXsym block, n ∈ ns) {t s : AState} (h : ARelOn ns ρ t s) :
    ARelOn ns ρ (runBlockA t (renameBlock ρ block)) (runBlockA s block) := by
  induction block generalizing t s with
  | nil => exact h
  | cons i is ih =>
    have hcons : blockNamesXsym (i :: is) = bNamesXsym i ++ blockNamesXsym is := by
      simp [blockNamesXsym, List.flatMap_cons]
    simp only [renameBlock, List.map_cons, runBlockA_cons] at ih ⊢
    exact ih (fun n hn => hsub n (hcons ▸ List.mem_append.mpr (Or.inr hn)))
      (evalInstrA_renameInstr_rel_on hinj h i
        (fun n hn => hsub n (hcons ▸ List.mem_append.mpr (Or.inl hn))))

/-! ## The compiled program through the bytes -/

/-- An instruction of the round-trip set is not a `loadSym`. -/
theorem loadSymFree_of_blockCovered6 (i : JInstr 64) (hc : blockCovered6 alloc i = true) :
    loadSymFree i = true := by
  cases i with
  | loadSym d sym =>
      simp [blockCovered6, blockCovered, decodableJ, newCovered6] at hc
  | _ => rfl

/-- **Compiled program through the shipped bytes.** For a program in scope, a state `s`
related to `σ` by `StateRel`, and a physical state `t` whose registers hold the values of
the block-level registers of `s` under `nameOf alloc`, with equal flags and memory: the
`encodeJBlock6` bytes of the compiled program decode to a block which, run on `t`, leaves
a nonzero value in the physical register of temporary 0 exactly when `p.run σ = true`. -/
theorem compileProg_bytes_correct (hL : LayoutOK L) (hA : AllocOK L alloc) (p : FProg)
    (hf : p.fits L = true) (hl : p.litsFit = true)
    (hinj : RenInjOn (tR L 0 :: blockNamesXsym (compileProg L p)) (nameOf alloc))
    {σ : FState} {s t : AState} (hR : StateRel L σ s)
    (ht : ARelOn (tR L 0 :: blockNamesXsym (compileProg L p)) (nameOf alloc) t s) :
    ∃ blk, decodeJStream6 (compileProg L p).length (encodeJBlock6 alloc (compileProg L p)) =
        some blk ∧
      ((runBlockA t blk).regs (nameOf alloc (tR L 0)) ≠ 0 ↔ p.run σ = true) := by
  refine ⟨_, compileProg_roundtrip hA p hf hl, ?_⟩
  rw [map_renameJ_eq_renameBlock alloc _
    (fun i hi => loadSymFree_of_blockCovered6 i (compileProg_covered hA p hf hl i hi))]
  have hrel := runBlockA_renameBlock_rel_on hinj (compileProg L p)
    (fun n hn => List.mem_cons_of_mem _ hn) ht
  rw [hrel.regsOn (tR L 0) List.mem_cons_self]
  exact compileProg_correct hL p hf hR

end VerifiedEval

end
