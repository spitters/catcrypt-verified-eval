/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.VerifiedDecideDemo
public meta import VerifiedEval.VerifiedDecideDemo

/-!
# An equational law of a finite magma decided on the machine model

A finite magma of order 8 is given by its Cayley table, a list of 64 entries read row by row:
`magmaOp T x y` is the entry at `8 * x + y`. Model checks of this kind settle
non-implications between equational laws: a table that satisfies one law and violates another
shows that the first law does not imply the second.

`lawProg` is a fragment program that decides the law `(y ◇ x) ◇ y = x` over all `x y < 8`. It
runs two nested loops of 8 iterations and reads the table twice per pair, the second read at
an index computed from the first. `lawDecide` registers it as a `DecisionProc` for
`SatisfiesLaw`, each table entry one 64-bit cell.

`rotTable` is the table of `x ◇ y = rot x ⊕ rot² y` on 3-bit words, where `rot` rotates left
by one bit. `rotTable_law` proves by `verified_decide lawDecide` that it satisfies the law, and
`rotTable_not_comm` and `rotTable_not_assoc` exhibit pairs and triples at which it is neither
commutative nor associative. Together they show that the law `(y ◇ x) ◇ y = x` implies neither
commutativity nor associativity.

## Cost

Measured with `set_option profiler true` in the language server, on one elaboration each:
`verified_decide lawDecide` spends 5.6 s interpreting the run of the machine model on the
compiled bytes and about 0.3 s in the remaining tactic, compilation and type-checking steps;
`unfold SatisfiesLaw; decide +kernel` on the same goal spends 6.15 s in kernel type checking.
`verified_decide` adds one axiom, the statement that the machine model accepts the bytes.

## Main definitions

* `magmaOp`, `SatisfiesLaw`: the operation of a Cayley table and the law.
* `lawProg`, `lawLayout`, `lawPlan`: the program, its layout and register plan.
* `lawDecide`: the registered decision procedure.
* `rotTable`: an 8-element model of the law.

## Main results

* `lawProg_run_eq`: on a table of 64 entries below 8 the program answers whether the law holds
  at every pair.
* `law_spec`: on admissible tables the program answers `true` exactly when `SatisfiesLaw`
  holds.
* `rotTable_law`: `rotTable` satisfies the law, by `verified_decide`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval

/-! ## The law -/

/-- The operation of the magma with Cayley table `T` on `{0, …, 7}`: the entry at
`8 * x + y`. -/
def magmaOp (T : List Nat) (x y : Nat) : Nat := T.getD (8 * x + y) 0

/-- The magma with Cayley table `T` satisfies `(y ◇ x) ◇ y = x` at all `x y < 8`. -/
def SatisfiesLaw (T : List Nat) : Prop :=
  ∀ x < 8, ∀ y < 8, magmaOp T (magmaOp T y x) y = x

/-! ## The program -/

/-- The index of `(y ◇ x) ◇ y` in the table span `t`: `8 * t[8 * y + x] + y`. -/
def lawIndex : FExpr :=
  .bin .add (.bin .shl (.spanGet "t" (.bin .add (.bin .shl (.var "y") (.lit 3)) (.var "x")))
    (.lit 3)) (.var "y")

/-- The inner loop body: `ok := (t[lawIndex] = x) ∧ ok`. -/
def lawInner : FStmt :=
  .assign "ok" (.bin .and (.bin .eq (.spanGet "t" lawIndex) (.var "x")) (.var "ok"))

/-- The law checked over the table span `t` of 64 cells, with result `ok`. -/
def lawProg : FProg where
  params := [("t", .span .w64 64)]
  locals := [("x", .word .w64), ("y", .word .w64), ("ok", .bool)]
  body := .seq (.assign "ok" (.lit 1)) (.forLit "x" 8 (.forLit "y" 8 lawInner))
  result := .var "ok"

/-! ## Semantics of the program -/

/-- The cells of a table: one 64-bit cell per entry. -/
def tableCells (T : List Nat) : List (BitVec 64) := T.map (BitVec.ofNat 64)

/-- The state shape the loops preserve: the span `t` holds the table and `ok` holds `ok`. -/
structure LawInv (T : List Nat) (st : FState) (ok : Bool) : Prop where
  t : st.bufs "t" = tableCells T
  ok : st.scalars "ok" = bv ok

/-- The check at the pair `(X, Y)`. -/
def lawAt (T : List Nat) (X Y : Nat) : Bool := decide (magmaOp T (magmaOp T Y X) Y = X)

theorem lawProg_widths_ok : lawProg.widths "ok" = .w8 := rfl
theorem lawProg_widths_t : lawProg.widths "t" = .w64 := rfl
theorem lawProg_widths_x : lawProg.widths "x" = .w64 := rfl
theorem lawProg_widths_y : lawProg.widths "y" = .w64 := rfl

theorem tableCells_getD (T : List Nat) (n : Nat) :
    (tableCells T).getD n 0 = BitVec.ofNat 64 (T.getD n 0) := by
  simp [tableCells, List.getD_eq_getElem?_getD]

theorem magmaOp_lt {T : List Nat} (hT : ∀ v ∈ T, v < 8) (x y : Nat) : magmaOp T x y < 8 := by
  unfold magmaOp
  rw [List.getD_eq_getElem?_getD]
  cases h : T[8 * x + y]? with
  | none => simp
  | some v => exact hT v (List.mem_of_getElem? h)

theorem lawInner_step {T : List Nat} (hT : ∀ v ∈ T, v < 8) {st : FState} {ok : Bool}
    (h : LawInv T st ok) {X : Nat} (hX : X < 8) (hx : st.scalars "x" = BitVec.ofNat 64 X)
    {Y : Nat} (hY : Y < 8) :
    LawInv T (lawInner.exec lawProg.widths (st.set "y" (BitVec.ofNat 64 Y))) (lawAt T X Y && ok)
      ∧ (lawInner.exec lawProg.widths (st.set "y" (BitVec.ofNat 64 Y))).scalars "x" =
        BitVec.ofNat 64 X := by
  obtain ⟨ht, hok⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [lawInner, FStmt.exec, FState.set, ht]
  · have m1 := magmaOp_lt hT Y X
    have c1 : (tableCells T)[((Y % 18446744073709551616) <<< 3 + X) % 18446744073709551616]?.getD
        0#64 = BitVec.ofNat 64 (magmaOp T Y X) := by
      rw [show ((Y % 18446744073709551616) <<< 3 + X) % 18446744073709551616 = 8 * Y + X by
        simp [Nat.shiftLeft_eq]; omega, ← List.getD_eq_getElem?_getD]
      exact tableCells_getD T _
    have m2 := magmaOp_lt hT (magmaOp T Y X) Y
    have e : BitVec.ofNat 64 (magmaOp T (magmaOp T Y X) Y) = BitVec.ofNat 64 X ↔
        magmaOp T (magmaOp T Y X) Y = X := by
      constructor
      · intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        omega
      · intro h
        rw [h]
    have c2 : (tableCells T)[((BitVec.ofNat 64 (magmaOp T Y X)).toNat <<< 3 + Y) %
        18446744073709551616]?.getD 0#64 = BitVec.ofNat 64 (magmaOp T (magmaOp T Y X) Y) := by
      rw [BitVec.toNat_ofNat, show ((magmaOp T Y X % 2 ^ 64) <<< 3 + Y) % 18446744073709551616 =
        8 * magmaOp T Y X + Y by simp [Nat.shiftLeft_eq]; omega, ← List.getD_eq_getElem?_getD]
      exact tableCells_getD T _
    simp only [lawInner, lawIndex, FState.set, FStmt.exec, FExpr.eval, FBinop.isCompare,
      Bool.false_eq_true, ↓reduceIte, FBinop.eval, ht, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, FExpr.width, FBinop.isShift, lawProg_widths_y, Option.getD_some,
      and_w64_mask, String.reduceEq, hx, lawProg_widths_x, Option.or_self, BitVec.toNat_add,
      BitVec.toNat_shiftLeft, Nat.add_mod_mod, Nat.mod_add_mod, BitVec.ofNat_eq_ofNat,
      List.getD_eq_getElem?_getD, lawProg_widths_t, hok, lawProg_widths_ok]
    rw [c1, c2, ite_bv, bv_and_mask, bv_mask]
    simp only [lawAt, e]
  · simp [lawInner, FStmt.exec, FState.set, hx]

theorem lawInner_loop {T : List Nat} (hT : ∀ v ∈ T, v < 8) {st : FState} {ok : Bool}
    (h : LawInv T st ok) {X : Nat} (hX : X < 8) (hx : st.scalars "x" = BitVec.ofNat 64 X) :
    ∀ n, n ≤ 8 →
      LawInv T ((FStmt.forLit "y" n lawInner).exec lawProg.widths st)
        ((List.range n).all (lawAt T X) && ok) ∧
      ((FStmt.forLit "y" n lawInner).exec lawProg.widths st).scalars "x" = BitVec.ofNat 64 X
  | 0, _ => by simpa using ⟨h, hx⟩
  | n + 1, hn => by
      rw [FStmt.exec_forLit_succ]
      obtain ⟨h', hx'⟩ := lawInner_loop hT h hX hx n (by omega)
      have := lawInner_step hT h' hX hx' (Y := n) (by omega)
      simpa [List.range_succ, List.all_append, Bool.and_assoc, Bool.and_comm,
        Bool.and_left_comm] using this

theorem lawOuter_loop {T : List Nat} (hT : ∀ v ∈ T, v < 8) {st : FState} {ok : Bool}
    (h : LawInv T st ok) :
    ∀ m, m ≤ 8 →
      LawInv T ((FStmt.forLit "x" m (FStmt.forLit "y" 8 lawInner)).exec lawProg.widths st)
        ((List.range m).all (fun X => (List.range 8).all (lawAt T X)) && ok)
  | 0, _ => by simpa using h
  | m + 1, hm => by
      rw [FStmt.exec_forLit_succ]
      have h' := lawOuter_loop hT h m (by omega)
      have hs : LawInv T (((FStmt.forLit "x" m (FStmt.forLit "y" 8 lawInner)).exec
          lawProg.widths st).set "x" (BitVec.ofNat 64 m))
          ((List.range m).all (fun X => (List.range 8).all (lawAt T X)) && ok) :=
        ⟨by simp [FState.set, h'.t], by simp [FState.set, h'.ok]⟩
      have := (lawInner_loop hT hs (X := m) (by omega) (by simp [FState.set]) 8 le_rfl).1
      simpa [List.range_succ, List.all_append, Bool.and_assoc, Bool.and_comm,
        Bool.and_left_comm] using this

/-- On a table whose entries are below 8 the program answers whether the law holds at every
pair `x y < 8`. -/
theorem lawProg_run_eq {T : List Nat} (hT : ∀ v ∈ T, v < 8) {σ : FState}
    (hσ : σ.bufs "t" = tableCells T) :
    lawProg.run σ = (List.range 8).all (fun X => (List.range 8).all (lawAt T X)) := by
  have h0 : LawInv T ((FStmt.assign "ok" (.lit 1)).exec lawProg.widths σ) true :=
    ⟨by simp [FStmt.exec, FState.set, hσ], by
      simp only [FStmt.exec, FState.set, FExpr.eval, lawProg_widths_ok, ↓reduceIte]; decide⟩
  have h := lawOuter_loop hT h0 8 le_rfl
  simp only [FProg.run]
  change ((FStmt.exec lawProg.widths (FStmt.forLit "x" 8 (FStmt.forLit "y" 8 lawInner))
    (FStmt.exec lawProg.widths (FStmt.assign "ok" (FExpr.lit 1)) σ)).scalars "ok" != 0) = _
  rw [h.ok, Bool.and_true, bv_ne_zero]

/-! ## Registration -/

/-- The layout of `lawProg`: register scalars `x`, `y`, `ok` and the span `t`. -/
def lawLayout : Layout := stdLayout ["x", "y", "ok"] ["t"]

/-- The register plan of `lawProg`: the roles its code names, with the temporaries off
`%rsp`. -/
def lawPlan : RegPlan :=
  [(.gThen 0, 4), (.sink, 3), (.len "t", 5), (.ptr "t", 6),
   (.var "x", 7), (.var "y", 8), (.var "ok", 9),
   (.tmp 0, 0), (.tmp 1, 1), (.tmp 2, 2), (.tmp 3, 10), (.tmp 4, 11), (.tmp 5, 12),
   (.tmp 6, 13), (.tmp 7, 14), (.tmp 8, 15)]

theorem lawProg_fitsL : lawProg.fitsL lawLayout (fun _ => 64) = true := by decide

theorem lawProg_litsFitL : lawProg.litsFitL = true := by decide

theorem lawProg_planCheck : planCheck lawLayout lawPlan lawProg = true := by decide

/-- The source state of a table: the span `t`, every scalar `0`. -/
def lawState (T : List Nat) : FState where
  scalars := fun _ => 0
  bufs := fun t => if t = "t" then tableCells T else []

/-- The admissible tables: 64 entries, each below 8. -/
def lawAdmit (T : List Nat) : Bool := decide (T.length = 64) && T.all (· < 8)

theorem lawAdmit_spec {T : List Nat} (hT : lawAdmit T = true) :
    T.length = 64 ∧ ∀ v ∈ T, v < 8 := by
  simpa [lawAdmit] using hT

theorem lawState_length {T : List Nat} (hT : lawAdmit T = true) :
    ∀ t ∈ lawLayout.spans, ((lawState T).bufs t).length ≤ 64 := by
  intro t ht
  simp only [lawLayout, stdLayout, List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht
  simp [lawState, tableCells, (lawAdmit_spec hT).1]

/-- **Specification of the law program.** On an admissible table the program answers `true`
exactly when the magma satisfies `(y ◇ x) ◇ y = x`. -/
theorem law_spec (T : List Nat) (hT : lawAdmit T = true) :
    lawProg.run (lawState T) = true ↔ SatisfiesLaw T := by
  rw [lawProg_run_eq (lawAdmit_spec hT).2 (by simp [lawState])]
  simp [SatisfiesLaw, lawAt, List.all_eq_true, List.mem_range]

/-- The law checker registered as a decision procedure for `SatisfiesLaw`. -/
def lawDecide : DecisionProc (List Nat) SatisfiesLaw where
  prog := lawProg
  layout := lawLayout
  plan := lawPlan
  cap := fun _ => 64
  toState := lawState
  admit := lawAdmit
  layoutOK := stdLayout_ok _ _
  fitsL := lawProg_fitsL
  litsFitL := lawProg_litsFitL
  planOK := lawProg_planCheck
  admit_capOK := fun _ hx t ht => lawState_length hx t ht
  admit_lenLt := fun _ hx t ht => by have := lawState_length hx t ht; omega
  spec := law_spec

/-! ## A model of the law -/

/-- The Cayley table of `x ◇ y = rot x ⊕ rot² y` on 3-bit words, `rot` the left rotation by
one bit. -/
def rotTable : List Nat :=
  [0, 4, 1, 5, 2, 6, 3, 7, 2, 6, 3, 7, 0, 4, 1, 5, 4, 0, 5, 1, 6, 2, 7, 3, 6, 2, 7, 3, 4, 0, 5, 1,
   1, 5, 0, 4, 3, 7, 2, 6, 3, 7, 2, 6, 1, 5, 0, 4, 5, 1, 4, 0, 7, 3, 6, 2, 7, 3, 6, 2, 5, 1, 4, 0]

/-- `rotTable` satisfies `(y ◇ x) ◇ y = x`. -/
theorem rotTable_law : SatisfiesLaw rotTable := by verified_decide lawDecide

/-- `rotTable` is not commutative: `0 ◇ 1 ≠ 1 ◇ 0`. -/
theorem rotTable_not_comm : magmaOp rotTable 0 1 ≠ magmaOp rotTable 1 0 := by decide

/-- `rotTable` is not associative: `(0 ◇ 0) ◇ 1 ≠ 0 ◇ (0 ◇ 1)`. -/
theorem rotTable_not_assoc :
    magmaOp rotTable (magmaOp rotTable 0 0) 1 ≠ magmaOp rotTable 0 (magmaOp rotTable 0 1) := by
  decide

end VerifiedEval

end
