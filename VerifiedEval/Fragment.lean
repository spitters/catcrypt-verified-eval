/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

/-!
# The decision-procedure fragment

The fragment of Lean in which a decision procedure is written so that the
verified pipeline can compile it and run it on hardware. This module gives

* the grammar, as the inductives `FWidth`, `FTy`, `FBinop`, `FExpr`, `FStmt`
  and the program record `FProg`;
* the well-formedness checker `FProg.wf`, a total decision procedure for
  scoping and typing whose every rejection is a named `FragmentGap`;
* the denotational semantics `FExpr.eval`, `FStmt.exec` and `FProg.run`, total
  by structural recursion, over `FState`.

Values are fixed-width unsigned words held as 64-bit vectors; a narrower
width is enforced by `wf` (literal ranges, shift amounts) and by masking every
arithmetic result (`FExpr.eval`) and every assignment (`FStmt.exec`) at the
declared width. A `span` is a fixed-capacity buffer of
fixed-width cells and stands for `Array UIntN`, `ByteArray` and ASCII strings
alike; a `tagged` value is a tag byte with a word payload and stands for
`Option UIntN`. Loops are bounded: a literal trip count (`forLit`) or the
length of a span (`forLen`). There is no `while`.

The reifier from Lean terms into this grammar is
`VerifiedEval.FragmentReflect`.

## Main definitions

* `FProg`, `FStmt`, `FExpr`, `FTy`: the fragment grammar.
* `FragmentGap`: the named rejections.
* `FProg.wf`: the scoping and typing check.
* `FStmt.exec`, `FProg.run`: the total denotational semantics.

## Main results

* `wf_params_unique`: a well-formed program has distinct parameter names.
* `FStmt.exec_seq`, `FStmt.exec_forLit_succ`: the unfolding equations of sequencing and bounded loops.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval

/-! ## Grammar -/

/-- A machine word width. -/
inductive FWidth
  | w8 | w16 | w32 | w64
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Byte count of a width. -/
def FWidth.bytes : FWidth → Nat
  | .w8 => 1
  | .w16 => 2
  | .w32 => 4
  | .w64 => 8

/-- Bit count of a width. -/
def FWidth.bits (w : FWidth) : Nat := 8 * w.bytes

/-- The 64-bit mask selecting the low `w.bits` bits. -/
def FWidth.mask (w : FWidth) : BitVec 64 := BitVec.ofNat 64 (2 ^ w.bits - 1)

/-- A width's name as it appears in messages. -/
def FWidth.toString : FWidth → String
  | .w8 => "w8"
  | .w16 => "w16"
  | .w32 => "w32"
  | .w64 => "w64"

instance : ToString FWidth := ⟨FWidth.toString⟩

/-- A fragment type: a word, a boolean, a fixed-capacity buffer of fixed-width
cells, or a tag byte with a word payload. -/
inductive FTy
  | word (w : FWidth)
  | bool
  | span (cell : FWidth) (cap : Nat)
  | tagged (tags : Nat) (payload : FWidth)
  deriving Repr, DecidableEq, Inhabited, BEq

/-- A type's name as it appears in messages. -/
def FTy.toString : FTy → String
  | .word w => s!"word {w}"
  | .bool => "bool"
  | .span c n => s!"span {c} {n}"
  | .tagged t p => s!"tagged {t} {p}"

instance : ToString FTy := ⟨FTy.toString⟩

/-- The width at which a value of this type is masked on assignment: a word's
own width, one byte for a boolean, the cell width of a span, the payload width
of a tagged value. -/
def FTy.width : FTy → FWidth
  | .word w => w
  | .bool => .w8
  | .span c _ => c
  | .tagged _ p => p

/-- A binary operator: wrapping arithmetic, bitwise operators, shifts by a
literal amount, and the unsigned comparisons. -/
inductive FBinop
  | add | sub | mul | and | or | xor | shl | shr | lt | eq | ule
  deriving Repr, DecidableEq, Inhabited, BEq

/-- An operator's name as it appears in messages. -/
def FBinop.toString : FBinop → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .and => "and"
  | .or => "or"
  | .xor => "xor"
  | .shl => "shl"
  | .shr => "shr"
  | .lt => "lt"
  | .eq => "eq"
  | .ule => "ule"

instance : ToString FBinop := ⟨FBinop.toString⟩

/-- Whether the operator is a comparison, so its result is a boolean. -/
def FBinop.isCompare : FBinop → Bool
  | .lt | .eq | .ule => true
  | _ => false

/-- Whether the operator is a shift, so its right operand is a literal amount. -/
def FBinop.isShift : FBinop → Bool
  | .shl | .shr => true
  | _ => false

/-- Whether the operator is defined on booleans as well as words. -/
def FBinop.onBool : FBinop → Bool
  | .and | .or | .xor | .eq => true
  | _ => false

/-- A scalar expression. `spanLen`, `spanGet`, `tagOf` and `payload` read a
named buffer or tagged value; buffers and tagged values are not themselves
expressions. -/
inductive FExpr
  | var (x : String)
  | lit (n : Nat)
  | bin (op : FBinop) (a b : FExpr)
  | not (a : FExpr)
  | spanLen (s : String)
  | spanGet (s : String) (i : FExpr)
  | tagOf (s : String)
  | payload (s : String)
  deriving Repr, DecidableEq, Inhabited, BEq

/-- A statement. Loops are bounded by a literal (`forLit`) or by the length of a
span at loop entry (`forLen`); `matchTag` dispatches on the tag of a tagged
value with a default arm. -/
inductive FStmt
  | skip
  | seq (a b : FStmt)
  | assign (x : String) (e : FExpr)
  | spanSet (s : String) (i v : FExpr)
  | ite (c : FExpr) (t e : FStmt)
  | forLit (i : String) (n : Nat) (body : FStmt)
  | forLen (i s : String) (body : FStmt)
  | matchTag (s : String) (arms : List (Nat × FStmt)) (default : FStmt)
  deriving Repr, Inhabited, BEq

/-- A fragment program: typed parameters, typed locals, a body and a boolean
result expression. -/
structure FProg where
  params : List (String × FTy)
  locals : List (String × FTy)
  body : FStmt
  result : FExpr
  deriving Repr, Inhabited, BEq

/-! ## Rejections -/

/-- Every reason a program, or a Lean term offered to the reifier, is outside
the fragment. The checker `FProg.wf` reports the scoping and typing gaps; the
reifier reports the surface gaps, each naming the offending head constant. -/
inductive FragmentGap
  /-- A name read or written that is neither a parameter nor a local. -/
  | unboundVar (x : String)
  /-- A name declared twice among the parameters and locals. -/
  | duplicateName (x : String)
  /-- An expression of one type where another was required. -/
  | typeMismatch (expected actual : FTy)
  /-- A literal too large for the width it is assigned at. -/
  | litTooWide (w : FWidth) (n : Nat)
  /-- A literal other than 0 or 1 assigned at type `bool`. -/
  | litNotBool (n : Nat)
  /-- A span or tagged name used where a scalar is required. -/
  | notAScalar (x : String)
  /-- A name read as a span that is not one. -/
  | notASpan (x : String)
  /-- A name read as a tagged value that is not one. -/
  | notTagged (x : String)
  /-- A span index whose type is not a word. -/
  | indexNotWord (s : String)
  /-- The program's result expression is not boolean. -/
  | resultNotBool (actual : FTy)
  /-- A condition that is not boolean. -/
  | condNotBool
  /-- An arithmetic or shift operator applied to booleans. -/
  | opNotOnBool (op : FBinop)
  /-- An ordering comparison applied to booleans. -/
  | compareOnBool (op : FBinop)
  /-- `not` applied to a non-boolean. -/
  | notOnNonBool
  /-- A shift whose amount is not a literal. -/
  | shiftAmountNotLiteral
  /-- A shift by a literal at or beyond the operand width. -/
  | shiftAmountTooLarge (w : FWidth) (n : Nat)
  /-- A loop variable whose type is not a word. -/
  | loopVarNotWord (i : String)
  /-- A `matchTag` arm whose tag is outside the tagged type's tag count. -/
  | armTagOutOfRange (s : String) (tag : Nat)
  /-- The reifier met a head constant outside the fragment. -/
  | unknownHead (c : String)
  /-- The reifier met a term form outside the fragment (a lambda, a sort, a
  projection, …), named by its kind. -/
  | unsupportedTerm (kind : String)
  /-- The reifier met a binder or accumulator type outside the fragment. -/
  | unsupportedType (ty : String)
  /-- A loop bound that is neither a literal nor the size of a span. -/
  | loopBoundNotStatic
  /-- `Nat` subtraction, whose truncation differs from wrapping `sub`. -/
  | natTruncatedSubtraction
  /-- A `Nat` operator other than `+` and the comparisons. -/
  | natOperator (op : String)
  /-- A `let` that binds a non-scalar value. -/
  | letOfNonScalar (x : String) (ty : String)
  /-- A `match` whose discriminant is not a tagged parameter. -/
  | matchNotOnTagged
  deriving Repr, DecidableEq, Inhabited, BEq

/-- The rejection's text. -/
def FragmentGap.toString : FragmentGap → String
  | .unboundVar x => s!"unboundVar {x}: `{x}` is neither a parameter nor a local"
  | .duplicateName x => s!"duplicateName {x}: `{x}` is declared twice"
  | .typeMismatch e a => s!"typeMismatch: expected {e}, found {a}"
  | .litTooWide w n => s!"litTooWide {w} {n}: literal {n} does not fit {w}"
  | .litNotBool n => s!"litNotBool {n}: literal {n} is not a boolean"
  | .notAScalar x => s!"notAScalar {x}: `{x}` is a span or tagged value"
  | .notASpan x => s!"notASpan {x}: `{x}` is not a span"
  | .notTagged x => s!"notTagged {x}: `{x}` is not a tagged value"
  | .indexNotWord s => s!"indexNotWord {s}: the index into `{s}` is not a word"
  | .resultNotBool a => s!"resultNotBool: the result has type {a}"
  | .condNotBool => "condNotBool: the condition is not boolean"
  | .opNotOnBool op => s!"opNotOnBool {op}: `{op}` is not defined on booleans"
  | .compareOnBool op => s!"compareOnBool {op}: `{op}` is not an ordering on booleans"
  | .notOnNonBool => "notOnNonBool: `not` applied to a non-boolean"
  | .shiftAmountNotLiteral => "shiftAmountNotLiteral: the shift amount is not a literal"
  | .shiftAmountTooLarge w n => s!"shiftAmountTooLarge {w} {n}: shift by {n} at width {w}"
  | .loopVarNotWord i => s!"loopVarNotWord {i}: loop variable `{i}` is not a word"
  | .armTagOutOfRange s t => s!"armTagOutOfRange {s} {t}: `{s}` has no tag {t}"
  | .unknownHead c => s!"unknownHead {c}: head constant `{c}` is outside the fragment"
  | .unsupportedTerm k => s!"unsupportedTerm {k}: term form `{k}` is outside the fragment"
  | .unsupportedType t => s!"unsupportedType {t}: type `{t}` is outside the fragment"
  | .loopBoundNotStatic => "loopBoundNotStatic: the loop bound is neither a literal nor a span size"
  | .natTruncatedSubtraction => "natTruncatedSubtraction: `Nat` subtraction truncates, `sub` wraps"
  | .natOperator op => s!"natOperator {op}: `{op}` on `Nat` is outside the fragment; only `+` and comparisons of `Nat` are in it"
  | .letOfNonScalar x t => s!"letOfNonScalar {x} {t}: `let {x}` binds a value of type `{t}`"
  | .matchNotOnTagged => "matchNotOnTagged: the discriminant is not a tagged parameter"

instance : ToString FragmentGap := ⟨FragmentGap.toString⟩

/-! ## Well-formedness -/

/-- A typing environment: the declared parameters and locals. -/
abbrev FEnv := List (String × FTy)

/-- The first name that occurs twice in the list, if any. -/
def findDup : List String → Option String
  | [] => none
  | x :: xs => if xs.contains x then some x else findDup xs

namespace FExpr

/-- The declared type of a name, or `unboundVar`. -/
def lookupTy (Γ : FEnv) (x : String) : Except FragmentGap FTy :=
  match Γ.lookup x with
  | some t => .ok t
  | none => .error (.unboundVar x)

/-- The type of a scalar name: a word or a boolean. -/
def scalarTy (Γ : FEnv) (x : String) : Except FragmentGap FTy := do
  match ← lookupTy Γ x with
  | .word w => pure (.word w)
  | .bool => pure .bool
  | _ => throw (.notAScalar x)

/-- The cell width of a span name. -/
def spanCell (Γ : FEnv) (s : String) : Except FragmentGap FWidth := do
  match ← lookupTy Γ s with
  | .span c _ => pure c
  | _ => throw (.notASpan s)

/-- The tag count and payload width of a tagged name. -/
def taggedShape (Γ : FEnv) (s : String) : Except FragmentGap (Nat × FWidth) := do
  match ← lookupTy Γ s with
  | .tagged t p => pure (t, p)
  | _ => throw (.notTagged s)

/-- Join two inferred types; `none` is the type of a bare literal, which takes
the type of the other side. -/
def unify : Option FTy → Option FTy → Except FragmentGap (Option FTy)
  | none, t => .ok t
  | t, none => .ok t
  | some a, some b => if a = b then .ok (some a) else .error (.typeMismatch a b)

/-- Whether an inferred type is a word or a bare literal. -/
def isWordish : Option FTy → Bool
  | none => true
  | some (.word _) => true
  | _ => false

mutual

/-- The type of an expression; `none` for a bare literal or an arithmetic
combination of bare literals. Width checks on literals happen in `check`. -/
def infer (Γ : FEnv) : FExpr → Except FragmentGap (Option FTy)
  | .var x => do pure (some (← scalarTy Γ x))
  | .lit _ => pure none
  | .bin op a b => do
      if op.isShift then
        match b with
        | .lit _ =>
          let ta ← infer Γ a
          if isWordish ta then pure ta else throw (.opNotOnBool op)
        | _ => throw .shiftAmountNotLiteral
      else
        let t ← unify (← infer Γ a) (← infer Γ b)
        if op.isCompare then
          match t with
          | some (.word w) => do check Γ a (.word w); check Γ b (.word w); pure (some .bool)
          | some .bool =>
              if op.onBool then pure (some .bool) else throw (.compareOnBool op)
          | none => pure (some .bool)
          | some t => throw (.typeMismatch (.word .w64) t)
        else
          match t with
          | some .bool => if op.onBool then pure (some .bool) else throw (.opNotOnBool op)
          | _ => pure t
  | .not a => do
      match ← infer Γ a with
      | some .bool => pure (some .bool)
      | _ => throw .notOnNonBool
  | .spanLen s => do let _ ← spanCell Γ s; pure (some (.word .w64))
  | .spanGet s i => do
      let c ← spanCell Γ s
      if isWordish (← infer Γ i) then pure (some (.word c)) else throw (.indexNotWord s)
  | .tagOf s => do let _ ← taggedShape Γ s; pure (some (.word .w8))
  | .payload s => do let (_, p) ← taggedShape Γ s; pure (some (.word p))

/-- Check an expression against a required type, including that every literal
fits the width it is used at. -/
def check (Γ : FEnv) : FExpr → FTy → Except FragmentGap Unit
  | .lit n, .word w => if n < 2 ^ w.bits then pure () else throw (.litTooWide w n)
  | .lit n, .bool => if n ≤ 1 then pure () else throw (.litNotBool n)
  | .lit _, t => throw (.typeMismatch t (.word .w64))
  | .bin op a b, t => do
      if op.isCompare then
        let _ ← infer Γ (.bin op a b)
        if t = .bool then pure () else throw (.typeMismatch t .bool)
      else
        if t = .bool ∧ !op.onBool then throw (.opNotOnBool op)
        check Γ a t
        if op.isShift then
          match b, t with
          | .lit n, .word w => if n < w.bits then pure () else throw (.shiftAmountTooLarge w n)
          | .lit _, _ => throw (.opNotOnBool op)
          | _, _ => throw .shiftAmountNotLiteral
        else check Γ b t
  | e, t => do
      match ← infer Γ e with
      | some t' => if t = t' then pure () else throw (.typeMismatch t t')
      | none => pure ()

end

end FExpr

namespace FStmt

open FExpr in
mutual

/-- Scoping and typing of a statement. -/
def wf (Γ : FEnv) : FStmt → Except FragmentGap Unit
  | .skip => pure ()
  | .seq a b => do wf Γ a; wf Γ b
  | .assign x e => do check Γ e (← scalarTy Γ x)
  | .spanSet s i v => do
      let c ← spanCell Γ s
      if !isWordish (← infer Γ i) then throw (.indexNotWord s)
      check Γ v (.word c)
  | .ite c t e => do
      match check Γ c .bool with
      | .ok () => pure ()
      | .error _ => throw .condNotBool
      wf Γ t
      wf Γ e
  | .forLit i _ body => do
      match ← lookupTy Γ i with
      | .word _ => pure ()
      | _ => throw (.loopVarNotWord i)
      wf Γ body
  | .forLen i s body => do
      match ← lookupTy Γ i with
      | .word _ => pure ()
      | _ => throw (.loopVarNotWord i)
      let _ ← spanCell Γ s
      wf Γ body
  | .matchTag s arms d => do
      let (tags, _) ← taggedShape Γ s
      wfArms Γ s tags arms
      wf Γ d

/-- Scoping and typing of the arms of a `matchTag` on a value with `tags`
tags. -/
def wfArms (Γ : FEnv) (s : String) (tags : Nat) :
    List (Nat × FStmt) → Except FragmentGap Unit
  | [] => pure ()
  | (k, b) :: rest => do
      if k < tags then pure () else throw (.armTagOutOfRange s k)
      wf Γ b
      wfArms Γ s tags rest

end

end FStmt

/-- Scoping and typing of a program: names are unique, the body is well formed
and the result is boolean. -/
def FProg.wf (p : FProg) : Except FragmentGap Unit := do
  let Γ : FEnv := p.params ++ p.locals
  match findDup (Γ.map Prod.fst) with
  | some x => throw (.duplicateName x)
  | none => pure ()
  p.body.wf Γ
  match FExpr.check Γ p.result .bool with
  | .ok () => pure ()
  | .error (.typeMismatch _ a) => throw (.resultNotBool a)
  | .error g => throw g

theorem findDup_none_nodup : ∀ l : List String, findDup l = none → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
      unfold findDup at h
      split at h
      · exact absurd h (by simp)
      · rename_i hc
        exact List.nodup_cons.mpr ⟨by simpa using hc, findDup_none_nodup xs h⟩

/-- A well-formed program declares each name once. -/
theorem wf_params_unique (p : FProg) (h : p.wf = .ok ()) :
    ((p.params ++ p.locals).map Prod.fst).Nodup := by
  apply findDup_none_nodup
  simp only [FProg.wf] at h
  split at h <;> simp_all [bind, Except.bind]

/-! ## Semantics -/

/-- A machine state: scalars by name, and buffers by name. A tagged value `s`
is held in `bufs s` as the two-cell buffer `[tag, payload]`. -/
structure FState where
  scalars : String → BitVec 64
  bufs : String → List (BitVec 64)

/-- The state with every scalar 0 and every buffer empty. -/
def FState.empty : FState := ⟨fun _ => 0, fun _ => []⟩

/-- Write a scalar. -/
def FState.set (st : FState) (x : String) (v : BitVec 64) : FState :=
  { st with scalars := fun y => if y = x then v else st.scalars y }

/-- Write a buffer. -/
def FState.setBuf (st : FState) (s : String) (b : List (BitVec 64)) : FState :=
  { st with bufs := fun y => if y = s then b else st.bufs y }

/-- Write a tagged value as its `[tag, payload]` buffer. -/
def FState.setTagged (st : FState) (s : String) (tag payload : BitVec 64) : FState :=
  st.setBuf s [tag, payload]

/-- The value of a binary operator on 64-bit words; comparisons yield 0 or 1. -/
def FBinop.eval : FBinop → BitVec 64 → BitVec 64 → BitVec 64
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shl, a, b => a <<< b.toNat
  | .shr, a, b => a >>> b.toNat
  | .lt, a, b => if a < b then 1 else 0
  | .eq, a, b => if a = b then 1 else 0
  | .ule, a, b => if a ≤ b then 1 else 0

/-- The width at which an expression's value wraps, given the width `Γ` of each
name: a variable's or cell's declared width, and for an arithmetic operator the
width of its first non-literal operand. `none` for a bare literal. -/
def FExpr.width (Γ : String → FWidth) : FExpr → Option FWidth
  | .var x => some (Γ x)
  | .lit _ => none
  | .bin op a b =>
      if op.isCompare then some .w8
      else if op.isShift then width Γ a
      else (width Γ a).or (width Γ b)
  | .not _ => some .w8
  | .spanLen _ => some .w64
  | .spanGet s _ => some (Γ s)
  | .tagOf _ => some .w8
  | .payload s => some (Γ s)

/-- The value of an expression, given the width `Γ` of each name. Arithmetic
results wrap at the expression's width; an out-of-range `spanGet` reads 0. -/
def FExpr.eval (Γ : String → FWidth) (st : FState) : FExpr → BitVec 64
  | .var x => st.scalars x
  | .lit n => BitVec.ofNat 64 n
  | .bin op a b =>
      let r := op.eval (a.eval Γ st) (b.eval Γ st)
      if op.isCompare then r
      else r &&& (((FExpr.bin op a b).width Γ).getD .w64).mask
  | .not a => if a.eval Γ st = 0 then 1 else 0
  | .spanLen s => BitVec.ofNat 64 (st.bufs s).length
  | .spanGet s i => (st.bufs s).getD (i.eval Γ st).toNat 0
  | .tagOf s => (st.bufs s).getD 0 0
  | .payload s => (st.bufs s).getD 1 0

/-- The assignment width of each name, as declared. -/
def FProg.widths (p : FProg) (x : String) : FWidth :=
  match (p.params ++ p.locals).lookup x with
  | some t => t.width
  | none => .w64

mutual

/-- The state after a statement, given the assignment width `Γ` of each name.
Assignments mask to the declared width; a loop's trip count is fixed at loop
entry. -/
def FStmt.exec (Γ : String → FWidth) : FStmt → FState → FState
  | .skip, st => st
  | .seq a b, st => b.exec Γ (a.exec Γ st)
  | .assign x e, st => st.set x (e.eval Γ st &&& (Γ x).mask)
  | .spanSet s i v, st =>
      st.setBuf s ((st.bufs s).set (i.eval Γ st).toNat (v.eval Γ st &&& (Γ s).mask))
  | .ite c t e, st => if c.eval Γ st = 0 then e.exec Γ st else t.exec Γ st
  | .forLit i n body, st =>
      (List.range n).foldl (fun st k => body.exec Γ (st.set i (BitVec.ofNat 64 k))) st
  | .forLen i s body, st =>
      (List.range (st.bufs s).length).foldl
        (fun st k => body.exec Γ (st.set i (BitVec.ofNat 64 k))) st
  | .matchTag s arms d, st =>
      match FStmt.execArms Γ ((st.bufs s).getD 0 0).toNat arms st with
      | some st' => st'
      | none => d.exec Γ st

/-- The state after the first arm whose tag is `tag`; `none` when no arm has
that tag. -/
def FStmt.execArms (Γ : String → FWidth) (tag : Nat) :
    List (Nat × FStmt) → FState → Option FState
  | [], _ => none
  | (k, b) :: rest, st => if k = tag then some (b.exec Γ st) else FStmt.execArms Γ tag rest st

end

/-- The program's answer: whether the result expression is nonzero after the
body. -/
def FProg.run (p : FProg) (st : FState) : Bool :=
  p.result.eval p.widths (p.body.exec p.widths st) != 0

@[simp] theorem FStmt.exec_skip (Γ : String → FWidth) (st : FState) :
    (FStmt.skip).exec Γ st = st := rfl

@[simp] theorem FStmt.exec_seq (Γ : String → FWidth) (a b : FStmt) (st : FState) :
    (FStmt.seq a b).exec Γ st = b.exec Γ (a.exec Γ st) := rfl

@[simp] theorem FStmt.exec_forLit_zero (Γ : String → FWidth) (i : String) (body : FStmt)
    (st : FState) : (FStmt.forLit i 0 body).exec Γ st = st := by
  simp [FStmt.exec]

@[simp] theorem FStmt.exec_forLit_succ (Γ : String → FWidth) (i : String) (n : Nat)
    (body : FStmt) (st : FState) :
    (FStmt.forLit i (n + 1) body).exec Γ st =
      body.exec Γ (((FStmt.forLit i n body).exec Γ st).set i (BitVec.ofNat 64 n)) := by
  simp [FStmt.exec, List.range_succ]

end VerifiedEval

end
