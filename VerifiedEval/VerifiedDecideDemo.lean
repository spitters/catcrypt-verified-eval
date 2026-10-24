/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.VerifiedDecide
public import VerifiedEval.ArenaTransfer
public meta import VerifiedEval.VerifiedDecide
public meta import VerifiedEval.ArenaTransfer

/-!
# A substring search decided on the machine model

`substrProg` is a fragment program deciding whether the span `n` occurs contiguously in the
span `h`, for `h` of at most 16 cells and `n` of at most 4 cells. The outer loop runs over
every start `i < 16` and the inner loop over every offset `j < 4`; an offset at or past the
needle's length counts as a match, and a start counts only when the needle ends inside the
haystack.

`substrDecide` registers it as a `DecisionProc` for `IsSubstr` over pairs of ASCII strings,
each character one 64-bit cell holding its byte. The plan holds the four scalars `i`, `j`,
`ok`, `f`, the length and cell-0 registers of the two spans, the sink, the depth-0 guard and
the temporaries 0 to 5 in the sixteen general-purpose registers, `%rsp` holding the guard.

`substr_hello` is closed by `verified_decide substrDecide`. Its axioms are those of
`Lean.ofReduceBool` and the standard three; the evaluated term is one application of
`machineAccepts` to the bytes, the length, the initial state and the result register of
`substrDecide`.

## Main definitions

* `substrProg`, `substrLayout`, `substrPlan`: the program, its layout and register plan.
* `IsSubstr`: `x.2` occurs as a substring of `x.1`.
* `substrDecide`: the registered decision procedure.

## Main results

* `substrProg_run_eq`, `any_foundAt_iff`: on a haystack of at most 16 cells and a needle of
  at most 4 cells, the program answers whether the needle occurs at some start.
* `infix_iff_index`: an occurrence `H = a ++ N ++ b` is a start `I` at which the needle's
  cells agree with the haystack's.
* `substr_spec`: on admissible ASCII strings the program answers `true` exactly when
  `IsSubstr` holds.
* `substr_hello`: `"lo w"` occurs in `"hello world"`, by `verified_decide`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval

/-! ## The program -/

/-- The inner loop body: `ok := (|n| ≤ j ∨ n[j] = h[i + j]) ∧ ok`. -/
def substrInner : FStmt :=
  .assign "ok" (.bin .and
    (.bin .or (.bin .ule (.spanLen "n") (.var "j"))
      (.bin .eq (.spanGet "n" (.var "j")) (.spanGet "h" (.bin .add (.var "i") (.var "j")))))
    (.var "ok"))

/-- The accumulation after the inner loop: `f := f ∨ (ok ∧ i + |n| ≤ |h|)`. -/
def substrUpdate : FStmt :=
  .assign "f" (.bin .or (.var "f")
    (.bin .and (.var "ok") (.bin .ule (.bin .add (.var "i") (.spanLen "n")) (.spanLen "h"))))

/-- The outer loop body: reset `ok`, run the inner loop over `j < 4`, accumulate into `f`. -/
def substrOuter : FStmt :=
  .seq (.assign "ok" (.lit 1)) (.seq (.forLit "j" 4 substrInner) substrUpdate)

/-- Substring search over the spans `h` (at most 16 cells) and `n` (at most 4 cells), with
result `f`. -/
def substrProg : FProg where
  params := [("h", .span .w8 16), ("n", .span .w8 4)]
  locals := [("i", .word .w64), ("j", .word .w64), ("ok", .bool), ("f", .bool)]
  body := .forLit "i" 16 substrOuter
  result := .var "f"

/-! ## Semantics of the program -/

/-- The word `1` for `true` and `0` for `false`. -/
def bv (b : Bool) : BitVec 64 := if b then 1#64 else 0#64

theorem bv_or_mask (a b : Bool) : (bv a ||| bv b) &&& FWidth.w8.mask = bv (a || b) := by
  cases a <;> cases b <;> decide

theorem bv_and_mask (a b : Bool) : (bv a &&& bv b) &&& FWidth.w8.mask = bv (a && b) := by
  cases a <;> cases b <;> decide

theorem bv_mask (a : Bool) : bv a &&& FWidth.w8.mask = bv a := by
  cases a <;> decide

theorem ite_bv (p : Prop) [Decidable p] : (if p then 1#64 else 0#64) = bv (decide p) := by
  by_cases h : p <;> simp [bv, h]

theorem bv_ne_zero (b : Bool) : (bv b != 0) = b := by cases b <;> decide

theorem ofNat_le_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ≤ BitVec.ofNat 64 b ↔ a ≤ b := by
  rw [BitVec.le_def, toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb]

section SubstrSem

variable (H N : List (BitVec 64))

/-- The inner match condition at start `I` and offset `j`. -/
def okAt (I j : Nat) : Bool := decide (N.length ≤ j) || decide (N.getD j 0 = H.getD (I + j) 0)

/-- The state shape the loops preserve: the spans are `H` and `N`, and the scalars `i`,
`ok`, `f` hold `I`, `ok`, `f`. -/
structure SubstrInv (st : FState) (I : Nat) (ok f : Bool) : Prop where
  h : st.bufs "h" = H
  n : st.bufs "n" = N
  i : st.scalars "i" = BitVec.ofNat 64 I
  ok : st.scalars "ok" = bv ok
  f : st.scalars "f" = bv f

end SubstrSem

theorem substr_widths_ok : substrProg.widths "ok" = .w8 := rfl
theorem substr_widths_f : substrProg.widths "f" = .w8 := rfl
theorem substr_widths_i : substrProg.widths "i" = .w64 := rfl
theorem substr_widths_j : substrProg.widths "j" = .w64 := rfl

theorem substrInner_step {H N : List (BitVec 64)} (hN : N.length ≤ 4)
    {st : FState} {I : Nat} {ok f : Bool} (hI : I < 16) (h : SubstrInv H N st I ok f)
    {j : Nat} (hj : j < 4) :
    SubstrInv H N (substrInner.exec substrProg.widths (st.set "j" (BitVec.ofNat 64 j))) I
      (ok && okAt H N I j) f := by
  obtain ⟨hh, hn, hi, hok, hf⟩ := h
  constructor
  all_goals simp [substrInner, FStmt.exec, FState.set, FExpr.eval, FExpr.width,
    FBinop.eval, FBinop.isCompare, FBinop.isShift, substr_widths_ok, substr_widths_i,
    substr_widths_j, hh, hn, hi, hok, hf, and_w64_mask]
  rw [Nat.mod_eq_of_lt (show N.length < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show j < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show I + j < 18446744073709551616 by omega), ite_bv, ite_bv, bv_or_mask,
    bv_and_mask, bv_mask]
  simp [okAt, Bool.and_comm]

theorem substrInner_loop {H N : List (BitVec 64)} (hN : N.length ≤ 4)
    {st : FState} {I : Nat} {ok f : Bool} (hI : I < 16) (h : SubstrInv H N st I ok f) :
    ∀ n, n ≤ 4 → SubstrInv H N ((FStmt.forLit "j" n substrInner).exec substrProg.widths st) I
      (ok && (List.range n).all (okAt H N I)) f
  | 0, _ => by simpa using h
  | n + 1, hn => by
      rw [FStmt.exec_forLit_succ]
      have := substrInner_step hN hI (substrInner_loop hN hI h n (by omega)) (j := n) (by omega)
      simpa [List.range_succ, List.all_append, Bool.and_assoc] using this

theorem substrUpdate_step {H N : List (BitVec 64)} (hH : H.length ≤ 16) (hN : N.length ≤ 4)
    {st : FState} {I : Nat} {ok f : Bool} (hI : I < 16) (h : SubstrInv H N st I ok f) :
    SubstrInv H N (substrUpdate.exec substrProg.widths st) I ok
      (f || (ok && decide (I + N.length ≤ H.length))) := by
  obtain ⟨hh, hn, hi, hok, hf⟩ := h
  constructor
  all_goals simp [substrUpdate, FStmt.exec, FState.set, FExpr.eval, FExpr.width,
    FBinop.eval, FBinop.isCompare, FBinop.isShift, substr_widths_f, substr_widths_i,
    hh, hn, hi, hok, hf, and_w64_mask]
  rw [BitVec.ofNat_add_ofNat, ite_bv, substr_widths_ok, bv_and_mask, bv_or_mask, bv_mask]
  simp only [ofNat_le_ofNat (show I + N.length < 2 ^ 64 by omega)
    (show H.length < 2 ^ 64 by omega)]

theorem substrOuter_step {H N : List (BitVec 64)} (hH : H.length ≤ 16) (hN : N.length ≤ 4)
    {st : FState} {I' : Nat} {ok f : Bool} (h : SubstrInv H N st I' ok f) {I : Nat} (hI : I < 16) :
    ∃ ok', SubstrInv H N (substrOuter.exec substrProg.widths (st.set "i" (BitVec.ofNat 64 I))) I ok'
      (f || ((List.range 4).all (okAt H N I) && decide (I + N.length ≤ H.length))) := by
  obtain ⟨hh, hn, -, -, hf⟩ := h
  have h2 : SubstrInv H N ((FStmt.assign "ok" (.lit 1)).exec substrProg.widths
      (st.set "i" (BitVec.ofNat 64 I))) I true f := by
    constructor <;> simp [FStmt.exec, FState.set, FExpr.eval, substr_widths_ok, hh, hn, hf]
    all_goals decide
  have h4 := substrUpdate_step hH hN hI (substrInner_loop hN hI h2 4 le_rfl)
  exact ⟨_, by simpa [substrOuter, FStmt.exec] using h4⟩

/-- A match of the needle at start `I`: every offset below 4 matches and the needle ends
inside the haystack. -/
def foundAt (H N : List (BitVec 64)) (I : Nat) : Bool :=
  (List.range 4).all (okAt H N I) && decide (I + N.length ≤ H.length)

theorem substrOuter_loop {H N : List (BitVec 64)} (hH : H.length ≤ 16) (hN : N.length ≤ 4)
    {σ : FState} {I₀ : Nat} {ok₀ : Bool} (h : SubstrInv H N σ I₀ ok₀ false) :
    ∀ m, m ≤ 16 → ∃ I ok, SubstrInv H N ((FStmt.forLit "i" m substrOuter).exec substrProg.widths σ)
      I ok ((List.range m).any (foundAt H N))
  | 0, _ => ⟨I₀, ok₀, by simpa using h⟩
  | m + 1, hm => by
      obtain ⟨I, ok, hI⟩ := substrOuter_loop hH hN h m (by omega)
      obtain ⟨ok', h'⟩ := substrOuter_step hH hN hI (I := m) (by omega)
      rw [FStmt.exec_forLit_succ]
      exact ⟨m, ok', by simpa [List.range_succ, List.any_append, foundAt] using h'⟩

/-- On a haystack of at most 16 cells and a needle of at most 4 cells, the program answers
whether the needle is found at some start below 16. -/
theorem substrProg_run_eq {H N : List (BitVec 64)} (hH : H.length ≤ 16) (hN : N.length ≤ 4)
    {σ : FState} {I₀ : Nat} {ok₀ : Bool} (h : SubstrInv H N σ I₀ ok₀ false) :
    substrProg.run σ = (List.range 16).any (foundAt H N) := by
  obtain ⟨I, ok, hI⟩ := substrOuter_loop hH hN h 16 le_rfl
  simp only [FProg.run]
  exact (congrArg (· != 0) hI.f).trans (bv_ne_zero _)

/-- An occurrence `H = a ++ N ++ b` is a start `I` with `I + |N| ≤ |H|` at which every cell
of `N` agrees with the cell of `H` at the same offset. -/
theorem infix_iff_index {α : Type} (H N : List α) :
    (∃ a b, H = a ++ N ++ b) ↔
      ∃ I, I + N.length ≤ H.length ∧ ∀ j < N.length, N[j]? = H[I + j]? := by
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨a.length, by simp, fun j hj => ?_⟩
    rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hj]
  · rintro ⟨I, hI, hN⟩
    have hN' : (H.drop I).take N.length = N := by
      apply List.ext_getElem?
      intro j
      by_cases hj : j < N.length
      · rw [List.getElem?_take, ite_eq_left hj, List.getElem?_drop, hN j hj]
      · rw [List.getElem?_take, ite_eq_right hj, List.getElem?_eq_none (by omega)]
    refine ⟨H.take I, H.drop (I + N.length), ?_⟩
    conv_lhs => rw [← List.take_append_drop I H, ← List.take_append_drop N.length (H.drop I)]
    rw [hN', List.drop_drop, List.append_assoc]

/-- `foundAt` at some start below 16 is the index form of an occurrence, for a haystack of
at most 16 cells and a needle of at most 4 cells. -/
theorem any_foundAt_iff {H N : List (BitVec 64)} (hH : H.length ≤ 16) (hN : N.length ≤ 4) :
    (List.range 16).any (foundAt H N) = true ↔
      ∃ I, I + N.length ≤ H.length ∧ ∀ j < N.length, N[j]? = H[I + j]? := by
  simp only [List.any_eq_true, List.mem_range, foundAt, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, okAt, Bool.or_eq_true]
  constructor
  · rintro ⟨I, -, hall, hle⟩
    refine ⟨I, hle, fun j hj => ?_⟩
    rcases hall j (by omega) with h | h
    · omega
    · rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem (by omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
        List.getElem?_eq_getElem (show I + j < H.length by omega), Option.getD_some] at h
      rw [h]
  · rintro ⟨I, hle, hall⟩
    by_cases h0 : N.length = 0
    · refine ⟨0, by omega, fun j _ => Or.inl (by omega), by omega⟩
    · refine ⟨I, by omega, fun j _ => ?_, hle⟩
      by_cases hj : j < N.length
      · right
        simp only [List.getD_eq_getElem?_getD, hall j hj]
      · left; omega

/-! ## Registration -/

/-- The layout of `substrProg`: register scalars `i`, `j`, `ok`, `f` and spans `h`, `n`. -/
def substrLayout : Layout := stdLayout ["i", "j", "ok", "f"] ["h", "n"]

/-- The register plan of `substrProg`: the sixteen roles its code names, with the
temporaries off `%rsp`. -/
def substrPlan : RegPlan :=
  [(.gThen 0, 4), (.sink, 3), (.len "h", 5), (.ptr "h", 6), (.len "n", 7), (.ptr "n", 8),
   (.var "i", 9), (.var "j", 10), (.var "ok", 11), (.var "f", 12),
   (.tmp 0, 0), (.tmp 1, 1), (.tmp 2, 2), (.tmp 3, 13), (.tmp 4, 14), (.tmp 5, 15)]

theorem substrProg_fitsL : substrProg.fitsL substrLayout (fun _ => 16) = true := by decide

theorem substrProg_litsFitL : substrProg.litsFitL = true := by decide

theorem substrProg_planCheck : planCheck substrLayout substrPlan substrProg = true := by decide

/-- The cells of an ASCII string: one 64-bit cell per character byte. -/
def cellsOf (s : String) : List (BitVec 64) := (asciiBytes s).map (BitVec.setWidth 64)

/-- The source state of a haystack and needle: spans `h` and `n`, every scalar `0`. -/
def substrState (x : String × String) : FState where
  scalars := fun _ => 0
  bufs := fun t => if t = "h" then cellsOf x.1 else if t = "n" then cellsOf x.2 else []

/-- The admissible inputs: a haystack of at most 16 and a needle of at most 4 characters,
all ASCII. -/
def substrAdmit (x : String × String) : Bool :=
  decide (x.1.length ≤ 16) && decide (x.2.length ≤ 4) && x.1.toList.all (·.toNat < 128) &&
    x.2.toList.all (·.toNat < 128)

/-- The string `x.2` occurs as a substring of `x.1`. -/
def IsSubstr (x : String × String) : Prop := ∃ a b : String, x.1 = a ++ x.2 ++ b

theorem setWidth_injective : Function.Injective (BitVec.setWidth 64 : BitVec 8 → BitVec 64) := by
  intro a b h
  have e := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth] at e
  have := a.isLt
  have := b.isLt
  exact BitVec.eq_of_toNat_eq (by omega)

theorem map_infix_iff {f : BitVec 8 → BitVec 64} (hf : Function.Injective f)
    (H N : List (BitVec 8)) :
    (∃ a b, H.map f = a ++ N.map f ++ b) ↔ ∃ a b, H = a ++ N ++ b := by
  simp only [infix_iff_index, List.length_map, List.getElem?_map,
    (Option.map_injective hf).eq_iff]

theorem substrAdmit_spec {x : String × String} (hx : substrAdmit x = true) :
    x.1.length ≤ 16 ∧ x.2.length ≤ 4 ∧ IsAscii x.1 ∧ IsAscii x.2 := by
  simp only [substrAdmit, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hx
  exact ⟨hx.1.1.1, hx.1.1.2, hx.1.2, hx.2⟩

theorem cellsOf_length (s : String) : (cellsOf s).length = s.length := by
  simp [cellsOf, asciiBytes, String.length_toList]

theorem substrState_length {x : String × String} (hx : substrAdmit x = true) :
    ∀ t ∈ substrLayout.spans, ((substrState x).bufs t).length ≤ 16 := by
  obtain ⟨h1, h2, -, -⟩ := substrAdmit_spec hx
  intro t ht
  simp only [substrLayout, stdLayout, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> simp [substrState, cellsOf_length] <;> omega

/-- **Specification of the substring program.** On admissible ASCII strings the program
answers `true` exactly when the needle occurs in the haystack. -/
theorem substr_spec (x : String × String) (hx : substrAdmit x = true) :
    substrProg.run (substrState x) = true ↔ IsSubstr x := by
  obtain ⟨h1, h2, hs, hn⟩ := substrAdmit_spec hx
  have hH : (cellsOf x.1).length ≤ 16 := by rw [cellsOf_length]; exact h1
  have hN : (cellsOf x.2).length ≤ 4 := by rw [cellsOf_length]; exact h2
  have inv : SubstrInv (cellsOf x.1) (cellsOf x.2) (substrState x) 0 false false :=
    ⟨by simp [substrState], by simp [substrState], rfl, rfl, rfl⟩
  rw [substrProg_run_eq hH hN inv, any_foundAt_iff hH hN, ← infix_iff_index, cellsOf, cellsOf,
    map_infix_iff setWidth_injective, ← spanSearch_iff, ← substring_iff_spanSearch _ _ hs hn]
  rfl

/-- The substring search registered as a decision procedure for `IsSubstr`. -/
def substrDecide : DecisionProc (String × String) IsSubstr where
  prog := substrProg
  layout := substrLayout
  plan := substrPlan
  cap := fun _ => 16
  toState := substrState
  admit := substrAdmit
  layoutOK := stdLayout_ok _ _
  fitsL := substrProg_fitsL
  litsFitL := substrProg_litsFitL
  planOK := substrProg_planCheck
  admit_capOK := fun _ hx t ht => substrState_length hx t ht
  admit_lenLt := fun _ hx t ht => by have := substrState_length hx t ht; omega
  spec := substr_spec

/-! ## Decided instances

The axiom list of `substr_hello` is pinned as a static check that `verified_decide`
contributes `Lean.ofReduceBool` and `Lean.trustCompiler` only. The false instance is pinned
as a static check of the tactic's failure message. -/

theorem substr_hello : IsSubstr ("hello world", "lo w") := by verified_decide substrDecide

/--
info: 'VerifiedEval.substr_hello' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound]
-/
#guard_msgs in
#print axioms substr_hello

/--
error: verified_decide: the machine returned false on
  machineAccepts substrDecide.bytes substrDecide.code.length (substrDecide.init ("hello world", "low"))
    substrDecide.resReg
-/
#guard_msgs in
example : IsSubstr ("hello world", "low") := by verified_decide substrDecide

end VerifiedEval

end
