/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import VerifiedEval.FragmentFixtures
public import VerifiedEval.FragmentFixtures
public import VerifiedEval.FragmentSpecTac

/-!
# Correctness theorems of the reified fixtures

For every fixture of `VerifiedEval.FragmentFixtures` reified from a Lean function,
`fragment_theorem` produces the theorem that the reified program computes the function on
every state agreeing with the encodings of the arguments; the bounded loops included. A
program altered after reification gets no theorem (the negative tests at the end).

## Main results

* `pAdd8_correct`, …, `pSubstring_correct`: one theorem per reified fixture.
* `pLitWrap_correct`, `pLit8_correct`, …, `pLitNat_correct`: arithmetic on literals at every
  width, folded by the reifier at the width of its type.
* `pAdd8Hand_correct`, `pSumHand_correct`: hand-written programs, by normalisation.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval.Fixtures

open VerifiedEval VerifiedEval.Spec

fragment_theorem pAdd8_correct : exAdd8 ~> pAdd8
fragment_theorem pSub16_correct : exSub16 ~> pSub16
fragment_theorem pMul32_correct : exMul32 ~> pMul32
fragment_theorem pAnd64_correct : exAnd64 ~> pAnd64
fragment_theorem pOr8_correct : exOr8 ~> pOr8
fragment_theorem pXor8_correct : exXor8 ~> pXor8
fragment_theorem pShl8_correct : exShl8 ~> pShl8
fragment_theorem pShr32_correct : exShr32 ~> pShr32
fragment_theorem pLt64_correct : exLt64 ~> pLt64
fragment_theorem pLe16_correct : exLe16 ~> pLe16
fragment_theorem pGt8_correct : exGt8 ~> pGt8
fragment_theorem pGe8_correct : exGe8 ~> pGe8
fragment_theorem pEq8_correct : exEq8 ~> pEq8
fragment_theorem pBne8_correct : exBne8 ~> pBne8
fragment_theorem pBoolAnd_correct : exBoolAnd ~> pBoolAnd
fragment_theorem pBoolOr_correct : exBoolOr ~> pBoolOr
fragment_theorem pBoolNot_correct : exBoolNot ~> pBoolNot
fragment_theorem pBoolXor_correct : exBoolXor ~> pBoolXor
fragment_theorem pBoolEq_correct : exBoolEq ~> pBoolEq
fragment_theorem pIteProp_correct : exIteProp ~> pIteProp
fragment_theorem pIteBool_correct : exIteBool ~> pIteBool
fragment_theorem pIteAnd_correct : exIteAnd ~> pIteAnd
fragment_theorem pIteNot_correct : exIteNot ~> pIteNot
fragment_theorem pCond_correct : exCond ~> pCond
fragment_theorem pIteExpr_correct : exIteExpr ~> pIteExpr
fragment_theorem pNestedLet_correct : exNestedLet ~> pNestedLet
fragment_theorem pSize_correct : exSize ~> pSize
fragment_theorem pGet_correct : exGet ~> pGet
fragment_theorem pByteArray_correct : exByteArray ~> pByteArray
fragment_theorem pNatAdd_correct : exNatAdd ~> pNatAdd
fragment_theorem pIsSome_correct : exIsSome ~> pIsSome
fragment_theorem pIsNone_correct : exIsNone ~> pIsNone
fragment_theorem pGetD_correct : exGetD ~> pGetD
fragment_theorem pMatch_correct : exMatch ~> pMatch
fragment_theorem pFoldLit_correct : exFoldLit ~> pFoldLit
fragment_theorem pNatFold_correct : exNatFold ~> pNatFold
fragment_theorem pFoldLen_correct : exFoldLen ~> pFoldLen
fragment_theorem pNatFoldLen_correct : exNatFoldLen ~> pNatFoldLen
fragment_theorem pFoldIndex_correct : exFoldIndex ~> pFoldIndex
fragment_theorem pSubstring_correct : substringSearch ~> pSubstring

/-! ## Further sources -/

/-- Equality and disequality of booleans as propositions. -/
def exBoolDeq (a b : Bool) : Bool := decide (a = b) && decide (a ≠ !b)
def pBoolDeq : FProg := reifyFragment% exBoolDeq
fragment_theorem pBoolDeq_correct : exBoolDeq ~> pBoolDeq

/-- A `Nat` parameter, a `Nat` loop and `Nat` comparisons. -/
def exNatLoop (n : Nat) (s : Array UInt16) : Bool :=
  (List.range s.size).foldl (fun ok i => ok && (i + n != s.size || s[i]! ≥ 3)) true
def pNatLoop : FProg := reifyFragment% exNatLoop
fragment_theorem pNatLoop_correct : exNatLoop ~> pNatLoop

/-- Nested conditionals in expression position over `UInt32` words. -/
def exNestedIte (x y : UInt32) : Bool :=
  (if x < y then (if x == 0 then y else x - 1) else y >>> 2) ^^^ 5 == x &&& 7
def pNestedIte : FProg := reifyFragment% exNestedIte
fragment_theorem pNestedIte_correct : exNestedIte ~> pNestedIte

/-! ## Hand-written programs

A program not in the reifier's shape gets its theorem by normalisation: the source is reified
with the program's result name, and the normal forms agree after the leading literal
assignments of the reified body are stripped; the theorem then assumes the state holds the
stripped values (`Holds`). -/

/-- `exAdd8` written by hand: no `skip` preludes, result local `r`. -/
def pAdd8Hand : FProg :=
  { params := [("x", .word .w8), ("y", .word .w8)], locals := [("z", .word .w8), ("r", .bool)],
    body := .seq (.assign "z" (.bin .add (.var "x") (.var "y")))
      (.assign "r" (.bin .eq (.var "z") (.lit 4))),
    result := .var "r" }
fragment_theorem pAdd8Hand_correct : exAdd8 ~> pAdd8Hand

/-- A sum by a loop whose accumulator `t` starts from the initial state. -/
def exSumHand (x : UInt8) : Bool :=
  (List.range 4).foldl (fun acc i => if i < 2 then acc + x else acc) 0 == x * 2
def sumHandBody : FStmt :=
  .ite (.bin .lt (.var "i") (.lit 2)) (.assign "t" (.bin .add (.var "t") (.var "x")))
    (.assign "t" (.var "t"))
def pSumHand : FProg :=
  { params := [("x", .word .w8)], locals := [("t", .word .w8), ("i", .word .w64), ("r", .bool)],
    body := .seq (.forLit "i" 4 sumHandBody)
      (.assign "r" (.bin .eq (.var "t") (.bin .mul (.var "x") (.lit 2)))),
    result := .var "r" }
fragment_theorem pSumHand_correct : exSumHand ~> pSumHand

/--
info: pSumHand_correct : ∀ (x : UInt8) (st : FState),
  Agree [("x", enc x)] [] st → Holds [("t", 0)] st → pSumHand.run st = exSumHand x
-/
#guard_msgs in
#check @pSumHand_correct

/-- `pSumHand` with its loop bound changed: no theorem. -/
def pSumHandAltered : FProg :=
  { pSumHand with
    body := .seq (.forLit "i" 1 sumHandBody)
      (.assign "r" (.bin .eq (.var "t") (.bin .mul (.var "x") (.lit 2)))) }
#guard pSumHand.run (stateOf [("x", 3)]) == exSumHand 3
#guard pSumHandAltered.run (stateOf [("x", 1), ("t", 0)]) != exSumHand 1

/-- info: no theorem; last failure: no lemma applies by normalisation: fragment_theorem: the normal form of the reified source is not that of the program -/
#guard_msgs in
fragment_theorem_rejects exSumHand ~> pSumHandAltered

/-! ## Axioms -/

/-- info: 'VerifiedEval.Fixtures.pSubstring_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pSubstring_correct

/-! ## Altered programs get no theorem -/

/-- Raise every literal of an expression by one. -/
def bumpLitsE : FExpr → FExpr
  | .lit n => .lit (n + 1)
  | .bin op a b => .bin op (bumpLitsE a) (bumpLitsE b)
  | .not a => .not (bumpLitsE a)
  | .spanGet s i => .spanGet s (bumpLitsE i)
  | e => e

/-- Raise every literal of the assignments of a statement, and every literal loop bound, by
one. -/
def bumpLits : FStmt → FStmt
  | .seq a b => .seq (bumpLits a) (bumpLits b)
  | .assign x e => .assign x (bumpLitsE e)
  | .ite c t e => .ite c (bumpLits t) (bumpLits e)
  | .forLit i n b => .forLit i (n + 1) (bumpLits b)
  | .forLen i s b => .forLen i s (bumpLits b)
  | s => s

/-- `pAdd8` with its compared literal raised: it answers differently on `(1, 3)`. -/
def pAdd8Altered : FProg := { pAdd8 with body := bumpLits pAdd8.body }
#guard pAdd8Altered.run (stateOf [("x", 1), ("y", 3)]) != exAdd8 1 3

/-- `pFoldLit` with its literals and its loop bound raised. -/
def pFoldLitAltered : FProg := { pFoldLit with body := bumpLits pFoldLit.body }
#guard pFoldLitAltered.run (stateOf [("x", 3)]) != exFoldLit 3

/-- `pSub16` with the operands of the subtraction swapped. -/
def pSub16Swapped : FProg :=
  { pSub16 with body := match pSub16.body with
    | .seq p (.assign r (.bin op (.bin .sub a b) c)) => .seq p (.assign r (.bin op (.bin .sub b a) c))
    | s => s }
#guard pSub16Swapped.run (stateOf [("x", 0), ("y", 1)]) != exSub16 0 1

/-! ## Arithmetic on literals at every width

An operator whose operands are both literals has no width in the fragment: its value wraps at
64 bits. The reifier folds it at the width of its type (and reduces a numeral of a word type
modulo `2 ^ w`), so the reified program answers as the source does and gets its theorem. -/

/-- Arithmetic on two literals at type `UInt8`. Before the fix the reifier produced an addition
at 64 bits (`pLitWrap64` below), answering `false` where the source answers `true`. -/
def exLitWrap (x : UInt8) : Bool := x == x && (200 + 100 : UInt8) == 44
def pLitWrap : FProg := reifyFragment% exLitWrap
#guard wfOk pLitWrap
#guard pLitWrap.run (stateOf [("x", 1)]) == exLitWrap 1
#guard exLitWrap 1
fragment_theorem pLitWrap_correct : exLitWrap ~> pLitWrap

/-- The program the reifier produced for `exLitWrap` before the fix (preludes omitted): the
addition of two literals, without width, at 64 bits. `FProg.wf` rejects it now. -/
def pLitWrap64 : FProg :=
  { pLitWrap with
    body := .assign "result" (.bin .and (.bin .eq (.var "x") (.var "x"))
      (.bin .eq (.bin .add (.lit 200) (.lit 100)) (.lit 44))) }
#guard wfGap? pLitWrap64 == some (.untypedArith .add)
#guard pLitWrap64.run (stateOf [("x", 1)]) != exLitWrap 1

/-- Literal arithmetic at `UInt8`: wrapping `+ - *`, a shift of a wrapped sum, a shift amount
beyond the width (Lean takes it modulo 8), a numeral beyond the width, bitwise operators, and a
literal sum under a variable. -/
def exLit8 (x : UInt8) : Bool :=
  x == x && (200 + 100 : UInt8) == 44 && (3 - 5 : UInt8) == 254 && (20 * 13 : UInt8) == 4 &&
    ((200 + 100 : UInt8) >>> 1) == 22 && ((1 : UInt8) <<< 9) == 2 && (300 : UInt8) == 44 &&
    ((0xF0 ||| 0x0F : UInt8) ^^^ 0xFF) == 0 && x + (250 + 10) == x + 4
def pLit8 : FProg := reifyFragment% exLit8
#guard exLit8 7
#guard wfOk pLit8
#guard pLit8.run (stateOf [("x", 7)]) == exLit8 7
#guard pLit8.run (stateOf [("x", 255)]) == exLit8 255
fragment_theorem pLit8_correct : exLit8 ~> pLit8

/-- Literal arithmetic at `UInt16`. -/
def exLit16 (x : UInt16) : Bool :=
  x == x && (65535 + 2 : UInt16) == 1 && (0 - 1 : UInt16) == 65535 &&
    (300 * 300 : UInt16) == 24464 && ((65535 + 3 : UInt16) >>> 1) == 1 &&
    ((1 : UInt16) <<< 17) == 2 && (65537 : UInt16) == 1 && x - (65535 + 1) == x
def pLit16 : FProg := reifyFragment% exLit16
#guard exLit16 9
#guard wfOk pLit16
#guard pLit16.run (stateOf [("x", 9)]) == exLit16 9
fragment_theorem pLit16_correct : exLit16 ~> pLit16

/-- Literal arithmetic at `UInt32`. -/
def exLit32 (x : UInt32) : Bool :=
  x == x && (4294967295 + 2 : UInt32) == 1 && (0 - 1 : UInt32) == 4294967295 &&
    (65536 * 65537 : UInt32) == 65536 && ((4294967295 + 3 : UInt32) >>> 1) == 1 &&
    ((1 : UInt32) <<< 33) == 2 && x * (65536 * 65536) == 0
def pLit32 : FProg := reifyFragment% exLit32
#guard exLit32 3
#guard wfOk pLit32
#guard pLit32.run (stateOf [("x", 3)]) == exLit32 3
fragment_theorem pLit32_correct : exLit32 ~> pLit32

/-- Literal arithmetic at `UInt64`, where the fragment's 64-bit words agree with the type. -/
def exLit64 (x : UInt64) : Bool :=
  x == x && (18446744073709551615 + 2 : UInt64) == 1 && (0 - 1 : UInt64) == 18446744073709551615 &&
    (4294967296 * 4294967297 : UInt64) == 4294967296 &&
    ((18446744073709551615 + 3 : UInt64) >>> 1) == 1 && ((1 : UInt64) <<< 65) == 2
def pLit64 : FProg := reifyFragment% exLit64
#guard exLit64 5
#guard wfOk pLit64
#guard pLit64.run (stateOf [("x", 5)]) == exLit64 5
fragment_theorem pLit64_correct : exLit64 ~> pLit64

/-- Literal arithmetic at `Nat`: a sum of numerals is folded without reduction. -/
def exLitNat (n : Nat) : Bool := n == n && (2 + 3 : Nat) == 5 && n + (1 + 1) == n + 2
def pLitNat : FProg := reifyFragment% exLitNat
#guard exLitNat 4
#guard wfOk pLitNat
#guard pLitNat.run (stateOf [("n", 4)]) == exLitNat 4
fragment_theorem pLitNat_correct : exLitNat ~> pLitNat

/-! ### The checker on arithmetic without width

`FProg.wf` rejects an operator without width whose 64-bit value is not masked afterwards (a
comparison operand, a condition, an index, the result), and accepts a sum, difference, product
or bitwise combination of literals whose value is masked at a width (the right-hand side of an
assignment or a span write, an operand of a typed operator). -/

#guard wfGap? (progOf [("x", .word .w8)] [("r", .bool)]
  (.assign "r" (.bin .eq (.var "x") (.bin .add (.lit 200) (.lit 100)))) (.var "r"))
  == some (.untypedArith .add)
#guard wfGap? (progOf [("x", .word .w8)] [("r", .word .w8)]
  (.assign "r" (.bin .shr (.bin .add (.lit 200) (.lit 100)) (.lit 1))) (.bin .eq (.var "r") (.lit 22)))
  == some (.untypedArith .shr)
#guard wfOk (progOf [("x", .word .w8)] [("r", .word .w8)]
  (.assign "r" (.bin .add (.var "x") (.bin .add (.lit 200) (.lit 100)))) (.bin .eq (.var "r") (.lit 44)))
#guard wfOk (progOf [("x", .word .w8)] [("r", .word .w8)]
  (.assign "r" (.bin .add (.lit 200) (.lit 100))) (.bin .eq (.var "r") (.lit 44)))

/-- info: no theorem; last failure: VerifiedEval.Spec.ExprTo.lit: fragment_theorem: side condition not closed 5#64 = VerifiedEval.Spec.enc 4 -/
#guard_msgs in
fragment_theorem_rejects exAdd8 ~> pAdd8Altered
/-- info: no theorem; last failure: no lemma applies by normalisation: fragment_theorem: the normal form of the reified source is not that of the program -/
#guard_msgs in
fragment_theorem_rejects exFoldLit ~> pFoldLitAltered
/-- info: no theorem; last failure: VerifiedEval.Spec.ExprTo.hoist: fragment_theorem: side condition not closed (List.map Prod.fst [("x", VerifiedEval.Spec.enc x), ("y", VerifiedEval.Spec.enc y)]).contains "y" = false -/
#guard_msgs in
fragment_theorem_rejects exSub16 ~> pSub16Swapped
/-- info: no theorem; last failure: no lemma applies by normalisation: fragment_theorem: the normal form of the reified source is not that of the program -/
#guard_msgs in
fragment_theorem_rejects exLitWrap ~> pLitWrap64

end VerifiedEval.Fixtures

end
