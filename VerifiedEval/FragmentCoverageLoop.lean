/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.FragmentCompileLoop
public import VerifiedEval.FragmentCoverage

/-!
# The compiled fragment with loops through the byte encoder and decoder

The loop compiler `compileProgL cap` of
`VerifiedEval.FragmentCompileLoop` unrolls every loop into
straight-line `JInstr 64` code. Besides the code forms of the loop-free compiler it emits the
length guard `lenGuard` (`mov`, `cmp`, `mov`, `cmovb`) and the loop-variable assignment
`loopVarCode`. This module proves that every instruction of the unrolled code is in the
decoder's covered set, so the shipped `encodeJBlock6` bytes decode back, and that the block
decoded from the bytes, run on a physical state related to the block-level state, answers as
the source program does.

## Scope

The immediates of the loop code are loop indices: `j < n` for a `forLit i n body` loop, and
`j < cap t` for a `forLen i t body` loop. `FStmt.fitsL` bounds `cap t ≤ 2 ^ 64`, so a
`forLen` index is below `2 ^ 64`; it does not bound `n`. `FStmt.litsFitL` is `FStmt.litsFit`
together with `n ≤ 2 ^ 64` for every `forLit` loop, and it agrees with `FStmt.litsFit` on
loop-free statements.

## Main definitions

* `FStmt.litsFitL`, `FStmt.litsFitArmsL`, `FProg.litsFitL`: every literal is below `2 ^ 64`
  and every `forLit` bound is at most `2 ^ 64`.

## Main results

* `lenGuard_fragOK`, `loopVarCode_fragOK`, `unrollLit_fragOK`, `unrollLen_fragOK`: the loop
  code is in the round-trip set.
* `compileProgL_covered`, `compileProgL_mulxRdxOk`: every instruction of
  `compileProgL L cap p` is in `blockCovered6 alloc` and satisfies `mulxRdxOk alloc`.
* `compileProgL_roundtrip`: the `encodeJBlock6` bytes of `compileProgL L cap p` decode to
  `(compileProgL L cap p).map (renameJ alloc)`.
* `compileProgL_bytes_correct`: the block decoded from the shipped bytes, run on a physical
  state related to a state `StateRel`-related to a source state `σ` with `CapOK L cap σ`,
  leaves a nonzero value in the physical register of temporary 0 exactly when
  `p.run σ = true`.
* `compileProgL_eq_compileProg_of_loopFree`, `FStmt.litsFitL_eq_litsFit_of_loopFree`: on a
  loop-free program the loop compiler and its literal scope are the loop-free ones.
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
open CatCrypt.Crypto.Optimizer.JInstrRegAllocScoped

/-! ## Literal scope with loops -/

mutual

/-- Every literal of every expression of the statement is below `2 ^ 64`, and every
`forLit` loop has a bound at most `2 ^ 64`. -/
def FStmt.litsFitL : FStmt → Bool
  | .skip => true
  | .seq a b => a.litsFitL && b.litsFitL
  | .assign _ e => e.litsFit
  | .spanSet _ i v => i.litsFit && v.litsFit
  | .ite c a b => c.litsFit && a.litsFitL && b.litsFitL
  | .matchTag _ arms dflt => FStmt.litsFitArmsL arms && dflt.litsFitL
  | .forLit _ n body => decide (n ≤ 2 ^ 64) && body.litsFitL
  | .forLen _ _ body => body.litsFitL

/-- Every arm satisfies `FStmt.litsFitL`. -/
def FStmt.litsFitArmsL : List (Nat × FStmt) → Bool
  | [] => true
  | (_, b) :: rest => b.litsFitL && FStmt.litsFitArmsL rest

end

/-- The program's body satisfies `FStmt.litsFitL` and every literal of its result is below
`2 ^ 64`. -/
def FProg.litsFitL (p : FProg) : Bool := p.body.litsFitL && p.result.litsFit

/-! ## Coverage of the loop code -/

variable {L : Layout} {alloc : GpAlloc}

theorem lenGuard_fragOK (g : RegName) (k : Nat) (t : String) (j : Nat) (hj : j < 2 ^ 64) :
    ∀ i ∈ lenGuard L g k t j, fragOK alloc i = true := by
  simp only [lenGuard, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  exact ⟨fragOK_mov_imm _ _ _ hj, fragOK_cmp_reg _ _ _, fragOK_mov_imm _ _ _ (by decide),
    fragOK_cmovb _ _ _⟩

theorem loopVarCode_fragOK (hA : AllocOK L alloc) (g : RegName) (i : String) (j : Nat)
    (hj : j < 2 ^ 64) : ∀ x ∈ loopVarCode L g i j, fragOK alloc x = true :=
  assignCode_fragOK hA _ g i (.lit j) rfl (by simpa only [FExpr.litsFit, decide_eq_true_eq] using hj)

theorem unrollLit_fragOK (hA : AllocOK L alloc) (g : RegName) (i : String)
    (c : List (JInstr 64)) (hc : ∀ x ∈ c, fragOK alloc x = true) :
    ∀ n, n ≤ 2 ^ 64 → ∀ x ∈ unrollLit L g i c n, fragOK alloc x = true
  | 0, _ => by simp [unrollLit]
  | n + 1, hn => by
      simp only [unrollLit, List.forall_mem_append]
      exact ⟨unrollLit_fragOK hA g i c hc n (by omega),
        loopVarCode_fragOK hA g i n (by omega), hc⟩

theorem unrollLen_fragOK (hA : AllocOK L alloc) (g : RegName) (k : Nat) (i t : String)
    (c : List (JInstr 64)) (hc : ∀ x ∈ c, fragOK alloc x = true) :
    ∀ m, m ≤ 2 ^ 64 → ∀ x ∈ unrollLen L g k i t c m, fragOK alloc x = true
  | 0, _ => by simp [unrollLen]
  | m + 1, hm => by
      simp only [unrollLen, List.forall_mem_append]
      exact ⟨unrollLen_fragOK hA g k i t c hc m (by omega),
        ⟨lenGuard_fragOK g k t m (by omega), loopVarCode_fragOK hA _ i m (by omega)⟩, hc⟩

/-! ## Coverage of the compiler with loops -/

mutual

/-- Every instruction of the code with loops of a statement in scope is in the round-trip
set. -/
theorem compileStmtL_fragOK (hA : AllocOK L alloc) (Γ : String → FWidth) (cap : String → Nat) :
    ∀ (st : FStmt) (k : Nat) (g : RegName), st.fitsL L cap = true → st.litsFitL = true →
      ∀ i ∈ compileStmtL L Γ cap k g st, fragOK alloc i = true
  | .skip, _, _, _, _ => by simp [compileStmtL]
  | .seq a c, k, g, hf, hl => by
      simp only [FStmt.fitsL, Bool.and_eq_true] at hf
      simp only [FStmt.litsFitL, Bool.and_eq_true] at hl
      simp only [compileStmtL, List.forall_mem_append]
      exact ⟨compileStmtL_fragOK hA Γ cap a k g hf.1 hl.1,
        compileStmtL_fragOK hA Γ cap c k g hf.2 hl.2⟩
  | .assign x e, _, g, hf, hl => by
      simp only [FStmt.fitsL] at hf
      simp only [FStmt.litsFitL] at hl
      simp only [compileStmtL]
      exact assignCode_fragOK hA Γ g x e hf hl
  | .spanSet t i v, _, g, hf, hl => by
      simp only [FStmt.fitsL, Bool.and_eq_true] at hf
      simp only [FStmt.litsFitL, Bool.and_eq_true] at hl
      simp only [compileStmtL]
      exact setCode_fragOK hA Γ g t i v hf.1.2 hf.2 hl.1 hl.2
  | .ite c a e, k, g, hf, hl => by
      simp only [FStmt.fitsL, Bool.and_eq_true] at hf
      simp only [FStmt.litsFitL, Bool.and_eq_true] at hl
      simp only [compileStmtL, List.forall_mem_append]
      exact ⟨⟨⟨compileExpr_fragOK hA Γ c 0 hf.1.1 hl.1.1, iteGuards_fragOK g k⟩,
        compileStmtL_fragOK hA Γ cap a (k + 1) _ hf.1.2 hl.1.2⟩,
        compileStmtL_fragOK hA Γ cap e (k + 1) _ hf.2 hl.2⟩
  | .matchTag t arms dflt, k, g, hf, hl => by
      simp only [FStmt.fitsL, Bool.and_eq_true] at hf
      simp only [FStmt.litsFitL, Bool.and_eq_true] at hl
      simp only [compileStmtL, List.forall_mem_append]
      exact ⟨⟨matchPrologue_fragOK hA g k t, compileArmsL_fragOK hA Γ cap arms k hf.1.2 hl.1⟩,
        compileStmtL_fragOK hA Γ cap dflt (k + 1) _ hf.2 hl.2⟩
  | .forLit i n body, k, g, hf, hl => by
      simp only [FStmt.fitsL] at hf
      simp only [FStmt.litsFitL, Bool.and_eq_true, decide_eq_true_eq] at hl
      simp only [compileStmtL]
      exact unrollLit_fragOK hA g i _ (compileStmtL_fragOK hA Γ cap body k g hf hl.2) n hl.1
  | .forLen i t body, k, g, hf, hl => by
      simp only [FStmt.fitsL, Bool.and_eq_true, decide_eq_true_eq] at hf
      simp only [FStmt.litsFitL] at hl
      simp only [compileStmtL]
      exact unrollLen_fragOK hA g k i t _
        (compileStmtL_fragOK hA Γ cap body (k + 1) _ hf.2 hl) (cap t) hf.1.2

/-- Every instruction of the code with loops of the arms of a `matchTag` in scope is in the
round-trip set. -/
theorem compileArmsL_fragOK (hA : AllocOK L alloc) (Γ : String → FWidth) (cap : String → Nat) :
    ∀ (arms : List (Nat × FStmt)) (k : Nat), FStmt.fitsArmsL L cap arms = true →
      FStmt.litsFitArmsL arms = true → ∀ i ∈ compileArmsL L Γ cap k arms, fragOK alloc i = true
  | [], _, _, _ => by simp [compileArmsL]
  | (tag, b) :: rest, k, hf, hl => by
      simp only [FStmt.fitsArmsL, Bool.and_eq_true, decide_eq_true_eq] at hf
      simp only [FStmt.litsFitArmsL, Bool.and_eq_true] at hl
      simp only [compileArmsL, List.forall_mem_append]
      exact ⟨⟨armGuards_fragOK k tag hf.1.1,
        compileStmtL_fragOK hA Γ cap b (k + 1) _ hf.1.2 hl.1⟩,
        compileArmsL_fragOK hA Γ cap rest k hf.2 hl.2⟩

end

/-- Every instruction of a compiled program with loops in scope is in the round-trip set. -/
theorem compileProgL_fragOK (hA : AllocOK L alloc) (cap : String → Nat) (p : FProg)
    (hf : p.fitsL L cap = true) (hl : p.litsFitL = true) :
    ∀ i ∈ compileProgL L cap p, fragOK alloc i = true := by
  simp only [FProg.fitsL, Bool.and_eq_true] at hf
  simp only [FProg.litsFitL, Bool.and_eq_true] at hl
  simp only [compileProgL, List.cons_append, List.forall_mem_cons, List.forall_mem_append]
  exact ⟨fragOK_mov_imm _ _ _ (by decide),
    compileStmtL_fragOK hA p.widths cap p.body 0 _ hf.1 hl.1,
    compileExpr_fragOK hA p.widths p.result 0 hf.2 hl.2⟩

/-- **Coverage with loops.** Every instruction of a compiled program with loops in scope is
in the round-trip set `blockCovered6 alloc`. -/
theorem compileProgL_covered (hA : AllocOK L alloc) (cap : String → Nat) (p : FProg)
    (hf : p.fitsL L cap = true) (hl : p.litsFitL = true) :
    ∀ i ∈ compileProgL L cap p, blockCovered6 alloc i = true :=
  fun i hi => by
    have h := compileProgL_fragOK hA cap p hf hl i hi
    simp only [fragOK, Bool.and_eq_true] at h
    exact h.1

/-- Every instruction of a compiled program with loops in scope satisfies
`mulxRdxOk alloc`. -/
theorem compileProgL_mulxRdxOk (hA : AllocOK L alloc) (cap : String → Nat) (p : FProg)
    (hf : p.fitsL L cap = true) (hl : p.litsFitL = true) :
    ∀ i ∈ compileProgL L cap p, mulxRdxOk alloc i = true :=
  fun i hi => by
    have h := compileProgL_fragOK hA cap p hf hl i hi
    simp only [fragOK, Bool.and_eq_true] at h
    exact h.2

/-- **Byte round trip with loops.** The shipped `encodeJBlock6` bytes of a compiled program
with loops in scope decode, instruction by instruction, to the compiled block with every
register name resolved through the allocation. -/
theorem compileProgL_roundtrip (hA : AllocOK L alloc) (cap : String → Nat) (p : FProg)
    (hf : p.fitsL L cap = true) (hl : p.litsFitL = true) :
    decodeJStream6 (compileProgL L cap p).length (encodeJBlock6 alloc (compileProgL L cap p)) =
      some ((compileProgL L cap p).map (renameJ alloc)) :=
  roundtrip_block6 alloc _ (compileProgL_covered hA cap p hf hl)
    (compileProgL_mulxRdxOk hA cap p hf hl)

/-- **Compiled program with loops through the shipped bytes.** For a program in the scope
with loops, a state `s` related by `StateRel` to a source state `σ` whose spans have lengths
at most their capacities, and a physical state `t` whose registers hold the values of the
block-level registers of `s` under `nameOf alloc`, with equal flags and memory: the
`encodeJBlock6` bytes of the compiled program decode to a block which, run on `t`, leaves a
nonzero value in the physical register of temporary 0 exactly when `p.run σ = true`. -/
theorem compileProgL_bytes_correct (hL : LayoutOK L) (hA : AllocOK L alloc)
    (cap : String → Nat) (p : FProg) (hf : p.fitsL L cap = true) (hl : p.litsFitL = true)
    (hinj : RenInjOn (tR L 0 :: blockNamesXsym (compileProgL L cap p)) (nameOf alloc))
    {σ : FState} {s t : AState} (hR : StateRel L σ s) (hC : CapOK L cap σ)
    (ht : ARelOn (tR L 0 :: blockNamesXsym (compileProgL L cap p)) (nameOf alloc) t s) :
    ∃ blk, decodeJStream6 (compileProgL L cap p).length
        (encodeJBlock6 alloc (compileProgL L cap p)) = some blk ∧
      ((runBlockA t blk).regs (nameOf alloc (tR L 0)) ≠ 0 ↔ p.run σ = true) := by
  refine ⟨_, compileProgL_roundtrip hA cap p hf hl, ?_⟩
  rw [map_renameJ_eq_renameBlock alloc _
    (fun i hi => loadSymFree_of_blockCovered6 i (compileProgL_covered hA cap p hf hl i hi))]
  have hrel := runBlockA_renameBlock_rel_on hinj (compileProgL L cap p)
    (fun n hn => List.mem_cons_of_mem _ hn) ht
  rw [hrel.regsOn (tR L 0) List.mem_cons_self]
  exact compileProgL_correct hL cap p hf hR hC

/-! ## Agreement with the loop-free scope -/

mutual

/-- On a loop-free statement the literal scope with loops is the loop-free literal scope. -/
theorem FStmt.litsFitL_eq_litsFit_of_loopFree :
    ∀ (st : FStmt), st.loopFree = true → st.litsFitL = st.litsFit
  | .skip, _ => rfl
  | .seq a b, h => by
      simp only [FStmt.loopFree, Bool.and_eq_true] at h
      simp only [FStmt.litsFitL, FStmt.litsFit, FStmt.litsFitL_eq_litsFit_of_loopFree a h.1,
        FStmt.litsFitL_eq_litsFit_of_loopFree b h.2]
  | .assign .., _ => rfl
  | .spanSet .., _ => rfl
  | .ite c a b, h => by
      simp only [FStmt.loopFree, Bool.and_eq_true] at h
      simp only [FStmt.litsFitL, FStmt.litsFit, FStmt.litsFitL_eq_litsFit_of_loopFree a h.1,
        FStmt.litsFitL_eq_litsFit_of_loopFree b h.2]
  | .matchTag t arms d, h => by
      simp only [FStmt.loopFree, Bool.and_eq_true] at h
      simp only [FStmt.litsFitL, FStmt.litsFit,
        FStmt.litsFitArmsL_eq_litsFitArms_of_loopFree arms h.1,
        FStmt.litsFitL_eq_litsFit_of_loopFree d h.2]
  | .forLit .., h => by simp [FStmt.loopFree] at h
  | .forLen .., h => by simp [FStmt.loopFree] at h

/-- On loop-free arms the literal scope with loops is the loop-free literal scope. -/
theorem FStmt.litsFitArmsL_eq_litsFitArms_of_loopFree :
    ∀ (arms : List (Nat × FStmt)), FStmt.loopFreeArms arms = true →
      FStmt.litsFitArmsL arms = FStmt.litsFitArms arms
  | [], _ => rfl
  | (tag, b) :: rest, h => by
      simp only [FStmt.loopFreeArms, Bool.and_eq_true] at h
      simp only [FStmt.litsFitArmsL, FStmt.litsFitArms,
        FStmt.litsFitL_eq_litsFit_of_loopFree b h.1,
        FStmt.litsFitArmsL_eq_litsFitArms_of_loopFree rest h.2]

end

/-- On a program with a loop-free body the compiler with loops is `compileProg`, for every
choice of capacities. -/
theorem compileProgL_eq_compileProg_of_loopFree (L : Layout) (cap : String → Nat) (p : FProg)
    (h : p.body.loopFree = true) : compileProgL L cap p = compileProg L p := by
  simp only [compileProgL, compileProg, compileStmtL_eq_of_loopFree L p.widths cap p.body 0 _ h]

end VerifiedEval

end
