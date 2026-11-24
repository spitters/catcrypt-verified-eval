/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.FragmentSpec

/-!
# Normal form of fragment statements

Hand-written fragment programs differ from the reifier's output in three ways that do not
change what they compute: the reifier writes a `skip` prelude before every expression it
assigns and nests sequences as the source's `let`s nest; it assigns a loop accumulator its
initial value where a hand-written program may rely on the initial state; and it names the
result local `result`.

`FStmt.norm` removes the first difference: it drops every `skip` and associates every sequence
to the right, and `FStmt.exec_norm` states that it preserves the semantics. `FStmt.stripInits`
removes leading assignments of literals, which a state that already holds those values does not
notice (`FStmt.exec_stripInits`). `StmtTo.ofNorm` and `run_ofNorm` transfer a judgment about
one statement to a statement with the same normal form after stripping; the third difference is
handled by reifying with the hand-written program's result name.

## Main definitions

* `FStmt.append`, `FStmt.norm`: the normal form.
* `FStmt.stripInits`: the leading literal assignments and the rest.
* `Spec.Holds`: a state holds the stripped values.

## Main results

* `FStmt.exec_append`, `FStmt.exec_norm`: the normal form preserves `exec`.
* `FStmt.exec_stripInits`: stripping is invisible on a state that holds the stripped values.
* `Spec.StmtTo.ofNorm`, `Spec.run_ofNorm`: transfer of the judgment and of the program's answer.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval

/-! ## The normal form -/

/-- Sequence a statement in normal form before another: a `skip` is dropped, and a sequence
is associated to the right. -/
def FStmt.append : FStmt → FStmt → FStmt
  | .skip, b => b
  | .seq a1 a2, b => .seq a1 (FStmt.append a2 b)
  | a, .skip => a
  | a, b => .seq a b

/-- The normal form of a statement: no `skip` inside a sequence, sequences associated to the
right, conditionals and loop bodies normalised. A `matchTag` is left as it is. -/
def FStmt.norm : FStmt → FStmt
  | .seq a b => FStmt.append (FStmt.norm a) (FStmt.norm b)
  | .ite c t e => .ite c (FStmt.norm t) (FStmt.norm e)
  | .forLit i n b => .forLit i n (FStmt.norm b)
  | .forLen i s b => .forLen i s (FStmt.norm b)
  | s => s

theorem FStmt.exec_append (Γ : String → FWidth) :
    ∀ (a b : FStmt) (st : FState), (FStmt.append a b).exec Γ st = b.exec Γ (a.exec Γ st)
  | .skip, b, st => rfl
  | .seq a1 a2, b, st => by
      simp only [FStmt.append, FStmt.exec_seq]
      exact FStmt.exec_append Γ a2 b _
  | .assign _ _, .skip, _ => rfl
  | .assign _ _, .seq _ _, _ => rfl
  | .assign _ _, .assign _ _, _ => rfl
  | .assign _ _, .spanSet _ _ _, _ => rfl
  | .assign _ _, .ite _ _ _, _ => rfl
  | .assign _ _, .forLit _ _ _, _ => rfl
  | .assign _ _, .forLen _ _ _, _ => rfl
  | .assign _ _, .matchTag _ _ _, _ => rfl
  | .spanSet _ _ _, .skip, _ => rfl
  | .spanSet _ _ _, .seq _ _, _ => rfl
  | .spanSet _ _ _, .assign _ _, _ => rfl
  | .spanSet _ _ _, .spanSet _ _ _, _ => rfl
  | .spanSet _ _ _, .ite _ _ _, _ => rfl
  | .spanSet _ _ _, .forLit _ _ _, _ => rfl
  | .spanSet _ _ _, .forLen _ _ _, _ => rfl
  | .spanSet _ _ _, .matchTag _ _ _, _ => rfl
  | .ite _ _ _, .skip, _ => rfl
  | .ite _ _ _, .seq _ _, _ => rfl
  | .ite _ _ _, .assign _ _, _ => rfl
  | .ite _ _ _, .spanSet _ _ _, _ => rfl
  | .ite _ _ _, .ite _ _ _, _ => rfl
  | .ite _ _ _, .forLit _ _ _, _ => rfl
  | .ite _ _ _, .forLen _ _ _, _ => rfl
  | .ite _ _ _, .matchTag _ _ _, _ => rfl
  | .forLit _ _ _, .skip, _ => rfl
  | .forLit _ _ _, .seq _ _, _ => rfl
  | .forLit _ _ _, .assign _ _, _ => rfl
  | .forLit _ _ _, .spanSet _ _ _, _ => rfl
  | .forLit _ _ _, .ite _ _ _, _ => rfl
  | .forLit _ _ _, .forLit _ _ _, _ => rfl
  | .forLit _ _ _, .forLen _ _ _, _ => rfl
  | .forLit _ _ _, .matchTag _ _ _, _ => rfl
  | .forLen _ _ _, .skip, _ => rfl
  | .forLen _ _ _, .seq _ _, _ => rfl
  | .forLen _ _ _, .assign _ _, _ => rfl
  | .forLen _ _ _, .spanSet _ _ _, _ => rfl
  | .forLen _ _ _, .ite _ _ _, _ => rfl
  | .forLen _ _ _, .forLit _ _ _, _ => rfl
  | .forLen _ _ _, .forLen _ _ _, _ => rfl
  | .forLen _ _ _, .matchTag _ _ _, _ => rfl
  | .matchTag _ _ _, .skip, _ => rfl
  | .matchTag _ _ _, .seq _ _, _ => rfl
  | .matchTag _ _ _, .assign _ _, _ => rfl
  | .matchTag _ _ _, .spanSet _ _ _, _ => rfl
  | .matchTag _ _ _, .ite _ _ _, _ => rfl
  | .matchTag _ _ _, .forLit _ _ _, _ => rfl
  | .matchTag _ _ _, .forLen _ _ _, _ => rfl
  | .matchTag _ _ _, .matchTag _ _ _, _ => rfl

/-- **The normal form preserves the semantics.** -/
theorem FStmt.exec_norm (Γ : String → FWidth) :
    ∀ (s : FStmt) (st : FState), (FStmt.norm s).exec Γ st = s.exec Γ st
  | .skip, _ => rfl
  | .seq a b, st => by
      simp only [FStmt.norm, FStmt.exec_seq]
      rw [FStmt.exec_append, FStmt.exec_norm Γ a, FStmt.exec_norm Γ b]
  | .assign _ _, _ => rfl
  | .spanSet _ _ _, _ => rfl
  | .ite c t e, st => by
      simp only [FStmt.norm, FStmt.exec]
      rw [FStmt.exec_norm Γ t, FStmt.exec_norm Γ e]
  | .forLit i n b, st => by
      simp only [FStmt.norm, FStmt.exec]
      congr 1
      funext σ k
      exact FStmt.exec_norm Γ b _
  | .forLen i s b, st => by
      simp only [FStmt.norm, FStmt.exec]
      congr 1
      funext σ k
      exact FStmt.exec_norm Γ b _
  | .matchTag _ _ _, _ => rfl

/-! ## Leading literal assignments -/

/-- At most `k` leading assignments of literals of a statement in normal form, as names and
literal values, and the rest. -/
def FStmt.stripInits : Nat → FStmt → List (String × Nat) × FStmt
  | k + 1, .seq (.assign x (.lit n)) rest =>
      let r := FStmt.stripInits k rest
      ((x, n) :: r.1, r.2)
  | _ + 1, .assign x (.lit n) => ([(x, n)], .skip)
  | _, s => ([], s)

/-- The number of leading assignments of literals of a statement in normal form. -/
def FStmt.countInits : FStmt → Nat
  | .seq (.assign _ (.lit _)) rest => FStmt.countInits rest + 1
  | .assign _ (.lit _) => 1
  | _ => 0

namespace Spec

/-- The state holds the word of each literal of `I` at its name. -/
def Holds (I : List (String × Nat)) (st : FState) : Prop :=
  ∀ p ∈ I, st.scalars p.1 = BitVec.ofNat 64 p.2

/-- Each literal of `I` fits the width of its name, so its assignment stores it unmasked. -/
def Fits (Γ : String → FWidth) (I : List (String × Nat)) : Prop :=
  ∀ p ∈ I, p.2 < 2 ^ (Γ p.1).bits

instance (Γ : String → FWidth) (I : List (String × Nat)) : Decidable (Fits Γ I) :=
  inferInstanceAs (Decidable (∀ p ∈ I, p.2 < 2 ^ (Γ p.1).bits))

theorem Holds.nil (st : FState) : Holds [] st := fun _ h => nomatch h

theorem FState.set_self (st : FState) (x : String) : st.set x (st.scalars x) = st := by
  obtain ⟨sc, bu⟩ := st
  simp only [FState.set, FState.mk.injEq, and_true]
  funext y
  split <;> simp_all

theorem ofNat_mask_of_lt (w : FWidth) {n : Nat} (h : n < 2 ^ w.bits) :
    BitVec.ofNat 64 n &&& w.mask = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [mask_toNat, BitVec.toNat_ofNat]
  have hb : w.bits ≤ 64 := by cases w <;> decide
  have : 2 ^ w.bits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hb
  rw [Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), Nat.mod_eq_of_lt h]

end Spec

open Spec in
/-- **Stripping is invisible on a state that holds the stripped values.** -/
theorem FStmt.exec_stripInits (Γ : String → FWidth) :
    ∀ (k : Nat) (s : FStmt) (st : FState), Fits Γ (FStmt.stripInits k s).1 →
      Holds (FStmt.stripInits k s).1 st → s.exec Γ st = (FStmt.stripInits k s).2.exec Γ st
  | 0, s, st, _, _ => by simp [FStmt.stripInits]
  | k + 1, s, st, hf, hh => by
      match s with
      | .seq (.assign x (.lit n)) rest =>
          simp only [FStmt.stripInits] at hf hh ⊢
          have hx : st.scalars x = BitVec.ofNat 64 n := hh (x, n) List.mem_cons_self
          have hn : n < 2 ^ (Γ x).bits := hf (x, n) List.mem_cons_self
          have hset : st.set x (BitVec.ofNat 64 n &&& (Γ x).mask) = st := by
            rw [ofNat_mask_of_lt _ hn, ← hx, FState.set_self]
          simp only [FStmt.exec, FExpr.eval, hset]
          exact FStmt.exec_stripInits Γ k rest st (fun p hp => hf p (List.mem_cons_of_mem _ hp))
            (fun p hp => hh p (List.mem_cons_of_mem _ hp))
      | .assign x (.lit n) =>
          simp only [FStmt.stripInits] at hf hh ⊢
          have hx : st.scalars x = BitVec.ofNat 64 n := hh (x, n) List.mem_cons_self
          have hn : n < 2 ^ (Γ x).bits := hf (x, n) List.mem_cons_self
          simp only [FStmt.exec, FExpr.eval]
          rw [ofNat_mask_of_lt _ hn, ← hx, FState.set_self]
      | .skip => rfl
      | .seq .skip _ => rfl
      | .seq (.seq _ _) _ => rfl
      | .seq (.assign _ (.var _)) _ => rfl
      | .seq (.assign _ (.bin _ _ _)) _ => rfl
      | .seq (.assign _ (.not _)) _ => rfl
      | .seq (.assign _ (.spanLen _)) _ => rfl
      | .seq (.assign _ (.spanGet _ _)) _ => rfl
      | .seq (.assign _ (.tagOf _)) _ => rfl
      | .seq (.assign _ (.payload _)) _ => rfl
      | .seq (.spanSet _ _ _) _ => rfl
      | .seq (.ite _ _ _) _ => rfl
      | .seq (.forLit _ _ _) _ => rfl
      | .seq (.forLen _ _ _) _ => rfl
      | .seq (.matchTag _ _ _) _ => rfl
      | .assign _ (.var _) => rfl
      | .assign _ (.bin _ _ _) => rfl
      | .assign _ (.not _) => rfl
      | .assign _ (.spanLen _) => rfl
      | .assign _ (.spanGet _ _) => rfl
      | .assign _ (.tagOf _) => rfl
      | .assign _ (.payload _) => rfl
      | .spanSet _ _ _ => rfl
      | .ite _ _ _ => rfl
      | .forLit _ _ _ => rfl
      | .forLen _ _ _ => rfl
      | .matchTag _ _ _ => rfl

namespace Spec

/-- **Transfer of a judgment.** A judgment about `q` holds of every statement `s` whose normal
form is that of `q` after `k` leading literal assignments are stripped, on the states that hold
the stripped values. -/
theorem StmtTo.ofNorm {Γ : String → FWidth} {L : SEnv} {B : BEnv} {q s : FStmt} {t : String}
    {v : BitVec 64} (k : Nat) (hq : StmtTo Γ L B q t v)
    (hn : (FStmt.stripInits k q.norm).2 = s.norm) (hf : Fits Γ (FStmt.stripInits k q.norm).1) :
    ∀ st, Agree L B st → Holds (FStmt.stripInits k q.norm).1 st →
      Agree ((t, v) :: L) B (s.exec Γ st) := by
  intro st hst hh
  rw [← FStmt.exec_norm, ← hn, ← FStmt.exec_stripInits Γ k _ st hf hh, FStmt.exec_norm]
  exact hq st hst

/-- **Transfer of the program's answer.** A judgment about a statement `q` whose normal form,
after `k` leading literal assignments are stripped, is that of the program's body gives the
program's answer on every state agreeing with the bindings and holding the stripped values. -/
theorem run_ofNorm {p : FProg} {L : SEnv} {B : BEnv} {r : String} {b : Bool} {q : FStmt}
    (k : Nat) (hr : p.result = .var r) (hq : StmtTo p.widths L B q r (enc b))
    (hn : (FStmt.stripInits k q.norm).2 = p.body.norm)
    (hf : Fits p.widths (FStmt.stripInits k q.norm).1) :
    ∀ st, Agree L B st → Holds (FStmt.stripInits k q.norm).1 st → p.run st = b := by
  intro st hst hh
  have := (StmtTo.ofNorm k hq hn hf st hst hh).1 r (enc b) (by simp [List.lookup])
  simp only [FProg.run, hr, FExpr.eval, this, enc_ne_zero]

/-- A judgment about `skip`: the target already holds its value. The reifier writes a loop
whose accumulator starts from its current value with a `skip` initialisation. -/
theorem StmtTo.skipSelf {Γ : String → FWidth} {L : SEnv} {B : BEnv} {t : String}
    {v : BitVec 64} (h : L.lookup t = some v) : StmtTo Γ L B .skip t v := by
  intro st hst
  have e : st.set t v = st := by rw [← hst.1 t v h, FState.set_self]
  rw [FStmt.exec_skip, ← e]
  exact hst.set t v

end Spec

end VerifiedEval

end
