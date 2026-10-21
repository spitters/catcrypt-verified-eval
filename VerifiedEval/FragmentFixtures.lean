/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.Fragment
public import VerifiedEval.FragmentReflect

/-!
# Fragment fixtures

One accepted and one rejected example for every grammar constructor and every
head the reifier covers. An accepted example is a Lean function in the
fragment's surface; the fixture pins that `reifyFragment%` accepts it, that the
reified program is well formed, and that `FProg.run` on a concrete input agrees
with the Lean function. A rejected example pins the elaboration error text, or
the `FragmentGap` that `FProg.wf` reports on a hand-built program.

The evaluations are static checks: each runs a few statements of the
denotational semantics on inputs of at most a dozen cells.

## Main results

* One accepted and one rejected example per grammar constructor and per reifier-covered head, including a byte-span substring search, checked by `#guard` and `#guard_msgs`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval.Fixtures

open VerifiedEval

/-! ## Helpers -/

/-- A state from named scalars and named buffers. -/
def stateOf (scal : List (String × Nat)) (bufs : List (String × List Nat) := []) : FState :=
  let st := scal.foldl (fun st (x, n) => st.set x (BitVec.ofNat 64 n)) FState.empty
  bufs.foldl (fun st (s, l) => st.setBuf s (l.map (BitVec.ofNat 64))) st

/-- Whether a program is well formed. -/
def wfOk (p : FProg) : Bool := p.wf.isOk

/-- The gap a program's checker reports, if any. -/
def wfGap? (p : FProg) : Option FragmentGap :=
  match p.wf with
  | .ok () => none
  | .error g => some g

/-- The 0/1 encoding of a boolean input. -/
def bit (b : Bool) : Nat := if b then 1 else 0

/-! ## Words and arithmetic -/

def exAdd8 (x y : UInt8) : Bool := let z := x + y; z == 4
def exSub16 (x y : UInt16) : Bool := (x - y) == 65535
def exMul32 (x y : UInt32) : Bool := x * y == 6
def exAnd64 (x y : UInt64) : Bool := (x &&& y) == 0
def exOr8 (x y : UInt8) : Bool := (x ||| y) == 255
def exXor8 (x y : UInt8) : Bool := (x ^^^ y) == 1
def exShl8 (x : UInt8) : Bool := (x <<< 4) == 16
def exShr32 (x : UInt32) : Bool := (x >>> 1) == 5
def exLt64 (x y : UInt64) : Bool := x < y
def exLe16 (x y : UInt16) : Bool := x ≤ y
def exGt8 (x y : UInt8) : Bool := x > y
def exGe8 (x y : UInt8) : Bool := x ≥ y
def exEq8 (x y : UInt8) : Bool := x == y
def exBne8 (x y : UInt8) : Bool := x != y

def pAdd8 : FProg := reifyFragment% exAdd8
#guard wfOk pAdd8
#guard pAdd8.params == [("x", .word .w8), ("y", .word .w8)]
#guard pAdd8.run (stateOf [("x", 250), ("y", 10)]) == exAdd8 250 10
#guard pAdd8.run (stateOf [("x", 1), ("y", 2)]) == exAdd8 1 2

def pSub16 : FProg := reifyFragment% exSub16
#guard wfOk pSub16
#guard pSub16.run (stateOf [("x", 0), ("y", 1)]) == exSub16 0 1
#guard pSub16.run (stateOf [("x", 5), ("y", 1)]) == exSub16 5 1

def pMul32 : FProg := reifyFragment% exMul32
#guard wfOk pMul32
#guard pMul32.run (stateOf [("x", 2), ("y", 3)]) == exMul32 2 3
#guard pMul32.run (stateOf [("x", 2147483648), ("y", 2)]) == exMul32 2147483648 2

def pAnd64 : FProg := reifyFragment% exAnd64
#guard wfOk pAnd64
#guard pAnd64.run (stateOf [("x", 12), ("y", 3)]) == exAnd64 12 3
#guard pAnd64.run (stateOf [("x", 12), ("y", 4)]) == exAnd64 12 4

def pOr8 : FProg := reifyFragment% exOr8
#guard wfOk pOr8
#guard pOr8.run (stateOf [("x", 240), ("y", 15)]) == exOr8 240 15

def pXor8 : FProg := reifyFragment% exXor8
#guard wfOk pXor8
#guard pXor8.run (stateOf [("x", 3), ("y", 2)]) == exXor8 3 2

def pShl8 : FProg := reifyFragment% exShl8
#guard wfOk pShl8
#guard pShl8.run (stateOf [("x", 1)]) == exShl8 1
#guard pShl8.run (stateOf [("x", 17)]) == exShl8 17

def pShr32 : FProg := reifyFragment% exShr32
#guard wfOk pShr32
#guard pShr32.run (stateOf [("x", 11)]) == exShr32 11

def pLt64 : FProg := reifyFragment% exLt64
#guard wfOk pLt64
#guard pLt64.run (stateOf [("x", 1), ("y", 2)]) == exLt64 1 2
#guard pLt64.run (stateOf [("x", 2), ("y", 2)]) == exLt64 2 2

def pLe16 : FProg := reifyFragment% exLe16
#guard wfOk pLe16
#guard pLe16.run (stateOf [("x", 2), ("y", 2)]) == exLe16 2 2
#guard pLe16.run (stateOf [("x", 3), ("y", 2)]) == exLe16 3 2

def pGt8 : FProg := reifyFragment% exGt8
#guard wfOk pGt8
#guard pGt8.run (stateOf [("x", 3), ("y", 2)]) == exGt8 3 2

def pGe8 : FProg := reifyFragment% exGe8
#guard wfOk pGe8
#guard pGe8.run (stateOf [("x", 1), ("y", 2)]) == exGe8 1 2

def pEq8 : FProg := reifyFragment% exEq8
#guard wfOk pEq8
#guard pEq8.run (stateOf [("x", 7), ("y", 7)]) == exEq8 7 7

def pBne8 : FProg := reifyFragment% exBne8
#guard wfOk pBne8
#guard pBne8.run (stateOf [("x", 7), ("y", 7)]) == exBne8 7 7
#guard pBne8.run (stateOf [("x", 7), ("y", 8)]) == exBne8 7 8

/-! ## Booleans and conditionals -/

def exBoolAnd (a b : Bool) : Bool := a && b
def exBoolOr (a b : Bool) : Bool := a || b
def exBoolNot (a : Bool) : Bool := !a
def exBoolXor (a b : Bool) : Bool := a ^^ b
def exBoolEq (a b : Bool) : Bool := a == b
def exIteProp (x : UInt8) : Bool := if x < 10 then true else false
def exIteBool (a : Bool) (x : UInt8) : Bool := if a then x == 1 else x == 2
def exIteAnd (x y : UInt8) : Bool := if x < 3 ∧ y ≤ 3 then true else false
def exIteNot (x : UInt8) : Bool := if ¬ (x = 3) then true else false
def exCond (a : Bool) : Bool := cond a false true
def exIteExpr (x y : UInt8) : Bool := (if x < y then x else y) == 3
def exNestedLet (x : UInt8) : Bool :=
  let r := if x < 5 then (let d := x + 1; d) else x
  r == 5

def pBoolAnd : FProg := reifyFragment% exBoolAnd
#guard wfOk pBoolAnd
#guard pBoolAnd.run (stateOf [("a", bit true), ("b", bit false)]) == exBoolAnd true false
#guard pBoolAnd.run (stateOf [("a", bit true), ("b", bit true)]) == exBoolAnd true true

def pBoolOr : FProg := reifyFragment% exBoolOr
#guard wfOk pBoolOr
#guard pBoolOr.run (stateOf [("a", bit false), ("b", bit true)]) == exBoolOr false true

def pBoolNot : FProg := reifyFragment% exBoolNot
#guard wfOk pBoolNot
#guard pBoolNot.run (stateOf [("a", bit false)]) == exBoolNot false

def pBoolXor : FProg := reifyFragment% exBoolXor
#guard wfOk pBoolXor
#guard pBoolXor.run (stateOf [("a", bit true), ("b", bit true)]) == exBoolXor true true
#guard pBoolXor.run (stateOf [("a", bit true), ("b", bit false)]) == exBoolXor true false

def pBoolEq : FProg := reifyFragment% exBoolEq
#guard wfOk pBoolEq
#guard pBoolEq.run (stateOf [("a", bit false), ("b", bit false)]) == exBoolEq false false

def pIteProp : FProg := reifyFragment% exIteProp
#guard wfOk pIteProp
#guard pIteProp.run (stateOf [("x", 9)]) == exIteProp 9
#guard pIteProp.run (stateOf [("x", 10)]) == exIteProp 10

def pIteBool : FProg := reifyFragment% exIteBool
#guard wfOk pIteBool
#guard pIteBool.run (stateOf [("a", bit false), ("x", 2)]) == exIteBool false 2
#guard pIteBool.run (stateOf [("a", bit true), ("x", 2)]) == exIteBool true 2

def pIteAnd : FProg := reifyFragment% exIteAnd
#guard wfOk pIteAnd
#guard pIteAnd.run (stateOf [("x", 2), ("y", 3)]) == exIteAnd 2 3
#guard pIteAnd.run (stateOf [("x", 2), ("y", 4)]) == exIteAnd 2 4

def pIteNot : FProg := reifyFragment% exIteNot
#guard wfOk pIteNot
#guard pIteNot.run (stateOf [("x", 3)]) == exIteNot 3
#guard pIteNot.run (stateOf [("x", 4)]) == exIteNot 4

def pCond : FProg := reifyFragment% exCond
#guard wfOk pCond
#guard pCond.run (stateOf [("a", bit true)]) == exCond true
#guard pCond.run (stateOf [("a", bit false)]) == exCond false

def pIteExpr : FProg := reifyFragment% exIteExpr
#guard wfOk pIteExpr
#guard pIteExpr.run (stateOf [("x", 3), ("y", 9)]) == exIteExpr 3 9
#guard pIteExpr.run (stateOf [("x", 9), ("y", 3)]) == exIteExpr 9 3

def pNestedLet : FProg := reifyFragment% exNestedLet
#guard wfOk pNestedLet
#guard pNestedLet.run (stateOf [("x", 4)]) == exNestedLet 4
#guard pNestedLet.run (stateOf [("x", 5)]) == exNestedLet 5

/-! ## Spans and tagged values -/

def exSize (s : Array UInt8) : Bool := s.size == 3
def exGet (s : Array UInt8) (i : Nat) : Bool := s[i]! == 9
def exByteArray (b : ByteArray) : Bool := b.size == 2 && b.get! 0 == 1
def exNatAdd (i : Nat) (s : Array UInt8) : Bool := i + 1 < s.size
def exIsSome (o : Option UInt8) : Bool := o.isSome
def exIsNone (o : Option UInt8) : Bool := o.isNone
def exGetD (o : Option UInt8) : Bool := o.getD 5 == 5
def exMatch (o : Option UInt16) : Bool := match o with | some v => v == 3 | none => false

def pSize : FProg := reifyFragment% exSize
#guard wfOk pSize
#guard pSize.run (stateOf [] [("s", [1, 2, 3])]) == exSize #[1, 2, 3]
#guard pSize.run (stateOf [] [("s", [1, 2])]) == exSize #[1, 2]

def pGet : FProg := reifyFragment% exGet
#guard wfOk pGet
#guard pGet.run (stateOf [("i", 1)] [("s", [1, 9, 3])]) == exGet #[1, 9, 3] 1
#guard pGet.run (stateOf [("i", 2)] [("s", [1, 9, 3])]) == exGet #[1, 9, 3] 2

def pByteArray : FProg := reifyFragment% exByteArray
#guard wfOk pByteArray
#guard pByteArray.run (stateOf [] [("b", [1, 7])]) == exByteArray ⟨#[1, 7]⟩
#guard pByteArray.run (stateOf [] [("b", [2, 7])]) == exByteArray ⟨#[2, 7]⟩

def pNatAdd : FProg := reifyFragment% exNatAdd
#guard wfOk pNatAdd
#guard pNatAdd.run (stateOf [("i", 1)] [("s", [1, 2, 3])]) == exNatAdd 1 #[1, 2, 3]
#guard pNatAdd.run (stateOf [("i", 2)] [("s", [1, 2, 3])]) == exNatAdd 2 #[1, 2, 3]

def pIsSome : FProg := reifyFragment% exIsSome
#guard wfOk pIsSome
#guard pIsSome.run (FState.empty.setTagged "o" 1 4) == exIsSome (some 4)
#guard pIsSome.run (FState.empty.setTagged "o" 0 0) == exIsSome none

def pIsNone : FProg := reifyFragment% exIsNone
#guard wfOk pIsNone
#guard pIsNone.run (FState.empty.setTagged "o" 0 0) == exIsNone none

def pGetD : FProg := reifyFragment% exGetD
#guard wfOk pGetD
#guard pGetD.run (FState.empty.setTagged "o" 1 4) == exGetD (some 4)
#guard pGetD.run (FState.empty.setTagged "o" 0 0) == exGetD none

def pMatch : FProg := reifyFragment% exMatch
#guard wfOk pMatch
#guard pMatch.run (FState.empty.setTagged "o" 1 3) == exMatch (some 3)
#guard pMatch.run (FState.empty.setTagged "o" 1 4) == exMatch (some 4)
#guard pMatch.run (FState.empty.setTagged "o" 0 0) == exMatch none

/-! ## Loops -/

def exFoldLit (x : UInt8) : Bool := (List.range 4).foldl (fun acc _ => acc + x) (0 : UInt8) == 12
def exNatFold (x : UInt64) : Bool := Nat.fold 3 (fun _ _ acc => acc * x) (1 : UInt64) == 8
def exFoldLen (s : Array UInt8) : Bool :=
  (List.range s.size).foldl (fun acc i => acc + s[i]!) (0 : UInt8) == 6
def exNatFoldLen (s : ByteArray) : Bool :=
  Nat.fold s.size (fun i _ ok => ok && s.get! i == 1) true
def exFoldIndex (s : Array UInt16) : Bool :=
  (List.range s.size).foldl (fun found i => found || (s[i]! == 5 && i < 2)) false

def pFoldLit : FProg := reifyFragment% exFoldLit
#guard wfOk pFoldLit
#guard pFoldLit.run (stateOf [("x", 3)]) == exFoldLit 3
#guard pFoldLit.run (stateOf [("x", 67)]) == exFoldLit 67

def pNatFold : FProg := reifyFragment% exNatFold
#guard wfOk pNatFold
#guard pNatFold.run (stateOf [("x", 2)]) == exNatFold 2
#guard pNatFold.run (stateOf [("x", 3)]) == exNatFold 3

def pFoldLen : FProg := reifyFragment% exFoldLen
#guard wfOk pFoldLen
#guard pFoldLen.run (stateOf [] [("s", [1, 2, 3])]) == exFoldLen #[1, 2, 3]
#guard pFoldLen.run (stateOf [] [("s", [255, 7])]) == exFoldLen #[255, 7]

def pNatFoldLen : FProg := reifyFragment% exNatFoldLen
#guard wfOk pNatFoldLen
#guard pNatFoldLen.run (stateOf [] [("s", [1, 1])]) == exNatFoldLen ⟨#[1, 1]⟩
#guard pNatFoldLen.run (stateOf [] [("s", [1, 2])]) == exNatFoldLen ⟨#[1, 2]⟩

def pFoldIndex : FProg := reifyFragment% exFoldIndex
#guard wfOk pFoldIndex
#guard pFoldIndex.run (stateOf [] [("s", [0, 5, 0])]) == exFoldIndex #[0, 5, 0]
#guard pFoldIndex.run (stateOf [] [("s", [0, 0, 5])]) == exFoldIndex #[0, 0, 5]

/-! ## Substring search -/

/-- Whether `needle` occurs contiguously in `hay`, written in the fragment's
surface: an outer loop over the start position and an inner loop comparing
cells. -/
def substringSearch (hay needle : Array UInt8) : Bool :=
  (List.range hay.size).foldl (fun found i =>
    let fits := i + needle.size ≤ hay.size
    let matched := (List.range needle.size).foldl
      (fun ok j => ok && (hay[i + j]! == needle[j]!)) true
    found || (fits && matched)) false

def pSubstring : FProg := reifyFragment% substringSearch
#guard wfOk pSubstring
#guard pSubstring.run (stateOf [] [("hay", [104, 101, 108, 108, 111]), ("needle", [108, 108])])
  == substringSearch #[104, 101, 108, 108, 111] #[108, 108]
#guard pSubstring.run (stateOf [] [("hay", [104, 101, 108, 108, 111]), ("needle", [108, 111, 1])])
  == substringSearch #[104, 101, 108, 108, 111] #[108, 111, 1]
#guard pSubstring.run (stateOf [] [("hay", [1, 2, 3]), ("needle", [3])])
  == substringSearch #[1, 2, 3] #[3]
#guard pSubstring.run (stateOf [] [("hay", [1, 2, 3]), ("needle", [])])
  == substringSearch #[1, 2, 3] #[]
#guard pSubstring.run (stateOf [] [("hay", []), ("needle", [1])])
  == substringSearch #[] #[1]

/-! ## Hand-built programs: `spanSet`, `matchTag` arms, `skip` -/

/-- Writes cell 0 of `s` to 300, then reads it back masked to a byte. -/
def pSpanSet : FProg :=
  { params := [("s", .span .w8 4)], locals := [("r", .bool)],
    body := .seq (.spanSet "s" (.lit 0) (.bin .add (.lit 255) (.lit 45)))
      (.assign "r" (.bin .eq (.spanGet "s" (.lit 0)) (.lit 44))),
    result := .var "r" }
#guard wfOk pSpanSet
#guard pSpanSet.run (stateOf [] [("s", [1, 2])]) == true

/-- Dispatches on a three-tag value with two arms and a default. -/
def pMatchTag : FProg :=
  { params := [("o", .tagged 3 .w32)], locals := [("r", .word .w32)],
    body := .matchTag "o" [(2, .assign "r" (.payload "o")), (1, .assign "r" (.lit 7))]
      (.seq .skip (.assign "r" (.lit 0))),
    result := .bin .eq (.var "r") (.lit 7) }
#guard wfOk pMatchTag
#guard pMatchTag.run (FState.empty.setTagged "o" 2 7) == true
#guard pMatchTag.run (FState.empty.setTagged "o" 2 8) == false
#guard pMatchTag.run (FState.empty.setTagged "o" 1 8) == true
#guard pMatchTag.run (FState.empty.setTagged "o" 0 7) == false

/-! ## Rejected by the reifier -/

/-- error: reifyFragment%: unknownHead HMod.hMod: head constant `HMod.hMod` is outside the fragment -/
#guard_msgs in
def rejMod : FProg := reifyFragment% (fun (x : UInt8) => x % 2 == 0)

/-- error: reifyFragment%: unknownHead HDiv.hDiv: head constant `HDiv.hDiv` is outside the fragment -/
#guard_msgs in
def rejDiv : FProg := reifyFragment% (fun (x : UInt32) => x / 2 == 0)

/-- error: reifyFragment%: unknownHead Complement.complement: head constant `Complement.complement` is outside the fragment -/
#guard_msgs in
def rejComplement : FProg := reifyFragment% (fun (x : UInt8) => ~~~x == 0)

/-- error: reifyFragment%: natTruncatedSubtraction: `Nat` subtraction truncates, `sub` wraps -/
#guard_msgs in
def rejNatSub : FProg := reifyFragment% (fun (i : Nat) => i - 1 == 0)

/-- error: reifyFragment%: natOperator HMul.hMul: `HMul.hMul` on `Nat` is outside the fragment; only `+` and comparisons of `Nat` are in it -/
#guard_msgs in
def rejNatMul : FProg := reifyFragment% (fun (i : Nat) => i * 2 == 0)

/-- error: reifyFragment%: shiftAmountNotLiteral: the shift amount is not a literal -/
#guard_msgs in
def rejShiftVar : FProg := reifyFragment% (fun (x k : UInt8) => x <<< k == 0)

/-- error: reifyFragment%: unsupportedType String: type `String` is outside the fragment -/
#guard_msgs in
def rejString : FProg := reifyFragment% (fun (s : String) => s.length == 0)

/-- error: reifyFragment%: unsupportedType List UInt8: type `List UInt8` is outside the fragment -/
#guard_msgs in
def rejList : FProg := reifyFragment% (fun (l : List UInt8) => l.length == 0)

/-- error: reifyFragment%: resultNotBool: the result has type word w64 -/
#guard_msgs in
def rejResultNat : FProg := reifyFragment% (fun (x : UInt64) => x + 1)

/-- error: reifyFragment%: loopBoundNotStatic: the loop bound is neither a literal nor a span size -/
#guard_msgs in
def rejLoopBound : FProg :=
  reifyFragment% (fun (n : Nat) => (List.range n).foldl (fun acc _ => acc + 1) (0 : UInt8) == 0)

/-- error: reifyFragment%: unknownHead Array.foldl: head constant `Array.foldl` is outside the fragment -/
#guard_msgs in
def rejArrayFoldl : FProg :=
  reifyFragment% (fun (s : Array UInt8) => s.foldl (fun acc x => acc + x) 0 == 0)

/-- error: reifyFragment%: unknownHead Prod.fst: head constant `Prod.fst` is outside the fragment -/
#guard_msgs in
def rejProjection : FProg :=
  reifyFragment% (fun (x : UInt8) =>
    ((List.range 2).foldl (fun (acc : UInt8 × UInt8) _ => (acc.2, acc.1 + x)) (0, 1)).1 == 0)

/-- error: reifyFragment%: letOfNonScalar t Array UInt8: `let t` binds a value of type `Array UInt8` -/
#guard_msgs in
def rejLetArray : FProg :=
  reifyFragment% (fun (s : Array UInt8) => let t := s.push 1; t.size == 2)

/-- error: reifyFragment%: unknownHead dite: head constant `dite` is outside the fragment -/
#guard_msgs in
def rejDite : FProg :=
  reifyFragment% (fun (x : UInt8) => if _ : x < 3 then true else false)

/-- error: reifyFragment%: unknownHead Dvd.dvd: head constant `Dvd.dvd` is outside the fragment -/
#guard_msgs in
def rejDvd : FProg := reifyFragment% (fun (x : Nat) => decide (2 ∣ x))

/-- error: reifyFragment%: unknownHead UInt8.toUInt64: head constant `UInt8.toUInt64` is outside the fragment -/
#guard_msgs in
def rejCoercion : FProg := reifyFragment% (fun (x : UInt8) => x.toUInt64 == 3)

/-- error: reifyFragment%: unknownHead Option.get!: head constant `Option.get!` is outside the fragment -/
#guard_msgs in
def rejOptionGet : FProg := reifyFragment% (fun (o : Option UInt8) => o.get! == 3)

/-- error: reifyFragment%: matchNotOnTagged: the discriminant is not a tagged parameter -/
#guard_msgs in
def rejMatchNat : FProg :=
  reifyFragment% (fun (n : Nat) => match n with | 0 => true | _ => false)

/-- error: reifyFragment%: unsupportedTerm tagged position holding a non-variable: term form `tagged position holding a non-variable` is outside the fragment -/
#guard_msgs in
def rejOptionIndex : FProg := reifyFragment% (fun (s : Array UInt8) => s[3]?.isSome)

/-- error: reifyFragment%: unknownHead Id.run: head constant `Id.run` is outside the fragment -/
#guard_msgs in
def rejDoBlock : FProg :=
  reifyFragment% (fun (x : UInt8) => Id.run do
    let mut acc := x
    acc := acc + 1
    return acc == 0)

/-- error: reifyFragment%: unknownHead Bool.toNat: head constant `Bool.toNat` is outside the fragment -/
#guard_msgs in
def rejBoolToNat : FProg := reifyFragment% (fun (a : Bool) => a.toNat == 1)

/-! ## Rejected by the checker -/

/-- A program whose only content is the given body and result over the given
environment. -/
def progOf (params locals : List (String × FTy)) (body : FStmt) (result : FExpr) : FProg :=
  { params, locals, body, result }

#guard wfGap? (progOf [("x", .word .w8)] [] (.assign "y" (.lit 1)) (.lit 1))
  == some (.unboundVar "y")
#guard wfGap? (progOf [("x", .word .w8), ("x", .bool)] [] .skip (.lit 1))
  == some (.duplicateName "x")
#guard wfGap? (progOf [("x", .word .w8), ("y", .word .w16)] [] (.assign "x" (.var "y")) (.lit 1))
  == some (.typeMismatch (.word .w8) (.word .w16))
#guard wfGap? (progOf [("x", .word .w8)] [] (.assign "x" (.lit 256)) (.lit 1))
  == some (.litTooWide .w8 256)
#guard wfGap? (progOf [("b", .bool)] [] (.assign "b" (.lit 2)) (.lit 1))
  == some (.litNotBool 2)
#guard wfGap? (progOf [("s", .span .w8 4)] [] .skip (.var "s"))
  == some (.notAScalar "s")
#guard wfGap? (progOf [("x", .word .w8)] [] .skip (.bin .eq (.spanLen "x") (.lit 0)))
  == some (.notASpan "x")
#guard wfGap? (progOf [("x", .word .w8)] [] .skip (.bin .eq (.tagOf "x") (.lit 0)))
  == some (.notTagged "x")
#guard wfGap? (progOf [("s", .span .w8 4), ("b", .bool)] [] .skip
    (.bin .eq (.spanGet "s" (.var "b")) (.lit 0)))
  == some (.indexNotWord "s")
#guard wfGap? (progOf [("x", .word .w8)] [] .skip (.var "x"))
  == some (.resultNotBool (.word .w8))
#guard wfGap? (progOf [("x", .word .w8)] [] (.ite (.var "x") .skip .skip) (.lit 1))
  == some .condNotBool
#guard wfGap? (progOf [("a", .bool), ("b", .bool)] [] (.assign "a" (.bin .add (.var "a") (.var "b")))
    (.lit 1))
  == some (.opNotOnBool .add)
#guard wfGap? (progOf [("a", .bool), ("b", .bool)] [] .skip (.bin .lt (.var "a") (.var "b")))
  == some (.compareOnBool .lt)
#guard wfGap? (progOf [("x", .word .w8)] [] .skip (.not (.var "x")))
  == some .notOnNonBool
#guard wfGap? (progOf [("x", .word .w8), ("k", .word .w8)] []
    (.assign "x" (.bin .shl (.var "x") (.var "k"))) (.lit 1))
  == some .shiftAmountNotLiteral
#guard wfGap? (progOf [("x", .word .w8)] [] (.assign "x" (.bin .shl (.var "x") (.lit 8))) (.lit 1))
  == some (.shiftAmountTooLarge .w8 8)
#guard wfGap? (progOf [("b", .bool)] [] (.forLit "b" 3 .skip) (.lit 1))
  == some (.loopVarNotWord "b")
#guard wfGap? (progOf [("o", .tagged 2 .w8)] [] (.matchTag "o" [(2, .skip)] .skip) (.lit 1))
  == some (.armTagOutOfRange "o" 2)
#guard wfGap? (progOf [("i", .word .w64), ("x", .word .w8)] [] (.forLen "i" "x" .skip) (.lit 1))
  == some (.notASpan "x")

/-! ## Semantics lemmas exercised -/

example (Γ : String → FWidth) (i : String) (b : FStmt) (st : FState) :
    (FStmt.forLit i 2 b).exec Γ st =
      b.exec Γ ((b.exec Γ (st.set i (BitVec.ofNat 64 0))).set i (BitVec.ofNat 64 1)) := by
  simp

end VerifiedEval.Fixtures

end
