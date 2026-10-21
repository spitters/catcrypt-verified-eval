/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import VerifiedEval.Fragment
public import VerifiedEval.Fragment
public import Lean

/-!
# Reifying Lean terms into the fragment

`reifyFragment% f` elaborates a Lean definition of the shape
`fun (x : UInt64) (s : Array UInt8) … => body` into a term of type `FProg`.
The body is a `let`-chain over the surface below, ending in a `Bool`; every
head outside it is rejected by an elaboration error naming the head constant
and the `FragmentGap`, never approximated.

## Surface

* Binder and `let` types: `UInt8`, `UInt16`, `UInt32`, `UInt64`, `Nat` (as a
  64-bit word), `Bool`, `Array UIntN` and `ByteArray` (spans of default
  capacity), `Option UIntN` (tagged, tag 1 = `some`).
* Word arithmetic `+ - * &&& ||| ^^^`, shifts `<<< >>>` by a literal, and the
  comparisons `< ≤ > ≥ == !=`; on `Nat` only `+` and the comparisons.
* `Bool` connectives `&& || ! ^^ ==`, `decide` of the comparison propositions,
  `if … then … else` on a boolean or on such a proposition, `cond`.
* `s.size`, `s[i]!`, `s.get!`, `o.isSome`, `o.getD d`, and `match o with
  | some v => … | none => …` on an `Option` parameter.
* Bounded loops `(List.range n).foldl (fun acc i => …) init` and
  `Nat.fold n (fun i _ acc => …) init` with `n` a literal or `s.size` and a
  scalar accumulator.

A conditional, loop or match in expression position is hoisted into a fresh
local. `reifyFragmentCore` is the `MetaM` entry the tactic layer calls.

## Main definitions

* `reifyFragmentCore`: the reifier from a Lean term to an `FProg`.
* `reifyFragment%`: the elaborator over `reifyFragmentCore`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval

open Lean Meta Elab

meta section

deriving instance ToExpr for FWidth
deriving instance ToExpr for FTy
deriving instance ToExpr for FBinop
deriving instance ToExpr for FExpr
deriving instance ToExpr for FStmt
deriving instance ToExpr for FProg

/-- The capacity assigned to a span reified from `Array UIntN` or `ByteArray`,
whose Lean type carries no bound. -/
def defaultSpanCap : Nat := 65536

/-- Reject with the gap's text. -/
def gapError {α : Type} (g : FragmentGap) : MetaM α :=
  throwError "reifyFragment%: {g.toString}"

/-- The reifier's environment: each bound Lean variable's fragment expression
and type. -/
abbrev ReifyEnv := List (FVarId × (FExpr × FTy))

/-- The reifier's accumulated locals and the names in use. -/
structure ReifySt where
  locals : Array (String × FTy) := #[]
  used : Array String := #[]
  fresh : Nat := 0

/-- The reifier monad. -/
abbrev ReifyM := ReaderT ReifyEnv (StateRefT ReifySt MetaM)

/-- Run a computation with a Lean variable bound to a fragment expression. -/
def withVar {α : Type} (x : FVarId) (e : FExpr) (t : FTy) (k : ReifyM α) : ReifyM α :=
  withReader (fun env => (x, (e, t)) :: env) k

/-- A name not yet in use, derived from `base`. -/
def freshName (base : Name) : ReifyM String := do
  let b := base.eraseMacroScopes.toString
  let b := if b.isEmpty ∨ b == "[anonymous]" then "t" else b
  let st ← get
  let name ←
    if st.used.contains b then
      let rec pick (k : Nat) (fuel : Nat) : String :=
        match fuel with
        | 0 => s!"{b}_{k}"
        | fuel + 1 => if st.used.contains s!"{b}_{k}" then pick (k + 1) fuel else s!"{b}_{k}"
      pure (pick st.fresh 1000)
    else pure b
  modify fun st => { st with used := st.used.push name, fresh := st.fresh + 1 }
  pure name

/-- Declare a local of the program. -/
def addLocal (x : String) (t : FTy) : ReifyM Unit :=
  modify fun st => { st with locals := st.locals.push (x, t) }

/-- The word width of a Lean scalar type, `Nat` counting as 64 bits. -/
def wordWidth? (ty : Expr) : Option FWidth :=
  match ty.consumeMData with
  | .const ``UInt8 _ => some .w8
  | .const ``UInt16 _ => some .w16
  | .const ``UInt32 _ => some .w32
  | .const ``UInt64 _ => some .w64
  | .const ``Nat _ => some .w64
  | _ => none

/-- The fragment type of a Lean type, if it has one. -/
def leanTyToFTy (ty : Expr) : MetaM (Option FTy) := do
  let ty := (← instantiateMVars ty).consumeMData
  if let some w := wordWidth? ty then return some (.word w)
  match ty with
  | .const ``Bool _ => return some .bool
  | .const ``ByteArray _ => return some (.span .w8 defaultSpanCap)
  | .app (.const ``Array _) a =>
      match wordWidth? a with
      | some w => return some (.span w defaultSpanCap)
      | none => return none
  | .app (.const ``Option _) a =>
      match wordWidth? a with
      | some w => return some (.tagged 2 w)
      | none => return none
  | _ => return none

/-- The fragment type of a Lean type, or `unsupportedType`. -/
def leanTyToFTy! (ty : Expr) : MetaM FTy := do
  match ← leanTyToFTy ty with
  | some t => pure t
  | none => gapError (.unsupportedType (toString (← ppExpr ty)))

/-- Whether a fragment type is a word or a boolean. -/
def FTy.isScalar : FTy → Bool
  | .word _ => true
  | .bool => true
  | _ => false

/-- The value of a literal: a raw or `OfNat` numeral, or `true`/`false`. -/
def litValue? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | .const ``Bool.true _ => some 1
  | .const ``Bool.false _ => some 0
  | e =>
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, .lit (.natVal n), _]) => some n
    | _ => none

/-- The Lean variable's fragment expression and type, or `unboundVar`. -/
def lookupVar (x : FVarId) : ReifyM (FExpr × FTy) := do
  match (← read).lookup x with
  | some r => pure r
  | none => gapError (.unboundVar (toString (← x.getUserName)))

/-- The name of a span-typed Lean variable, or `notASpan`. -/
def spanName (e : Expr) : ReifyM String := do
  match e.consumeMData with
  | .fvar x =>
      match ← lookupVar x with
      | (.var n, .span _ _) => pure n
      | (.var n, _) => gapError (.notASpan n)
      | _ => gapError (.notASpan (toString (← x.getUserName)))
  | _ => gapError (.unsupportedTerm "span position holding a non-variable")

/-- The name of a tagged Lean variable, or `notTagged`. -/
def taggedName (e : Expr) : ReifyM String := do
  match e.consumeMData with
  | .fvar x =>
      match ← lookupVar x with
      | (.var n, .tagged _ _) => pure n
      | (.var n, _) => gapError (.notTagged n)
      | _ => gapError (.notTagged (toString (← x.getUserName)))
  | _ => gapError (.unsupportedTerm "tagged position holding a non-variable")

/-- The kind of a term form outside the fragment. -/
def termKind (e : Expr) : String :=
  match e with
  | .lam .. => "lambda"
  | .forallE .. => "pi"
  | .sort .. => "sort"
  | .proj .. => "projection"
  | .mvar .. => "metavariable"
  | .letE .. => "let"
  | .app .. => "application of a non-constant"
  | .bvar .. => "loose bound variable"
  | _ => "other"

/-- Whether a Lean expression is an application of the given head with at least
`n` arguments. -/
def isHead (e : Expr) (c : Name) : Bool := e.getAppFn.isConstOf c

/-- The heads the statement walker handles directly; in expression position
they are hoisted into a fresh local. -/
def statementHeads : List Name :=
  [``ite, ``cond, ``List.foldl, ``Nat.fold, ``Option.getD]

mutual

/-- Reify an expression, together with the prelude statements its hoisted
subterms need. -/
partial def reifyExpr (e : Expr) : ReifyM (FStmt × FExpr) := do
  let e := e.consumeMData.headBeta
  if let some n := litValue? e then return (.skip, .lit n)
  match e with
  | .fvar x =>
      match ← lookupVar x with
      | (fe, t) => if t.isScalar then pure (.skip, fe) else gapError (.notAScalar (toString (← x.getUserName)))
  | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      match f with
      | .const c _ =>
          if statementHeads.contains c then hoist e
          else if let some info ← getMatcherInfo? c then
            let _ := info
            hoist e
          else reifyApp c args e
      | _ => gapError (.unsupportedTerm (termKind e))
  | _ => gapError (.unsupportedTerm (termKind e))

/-- Reify a conditional, loop or match met in expression position into a fresh
local assigned by a statement. -/
partial def hoist (e : Expr) : ReifyM (FStmt × FExpr) := do
  let ty ← inferType e
  let fty ← leanTyToFTy! ty
  unless fty.isScalar do gapError (.letOfNonScalar "t" (toString (← ppExpr ty)))
  let name ← freshName `t
  addLocal name fty
  let s ← reifyStmt name e
  pure (s, .var name)

/-- Reify a binary operator whose operand type is `α`. -/
partial def reifyBin (op : FBinop) (head : Name) (α a b : Expr) : ReifyM (FStmt × FExpr) := do
  match wordWidth? α with
  | none => gapError (.unsupportedType (toString (← ppExpr α)))
  | some _ =>
    if α.isConstOf ``Nat then
      if op == .sub then gapError .natTruncatedSubtraction
      if op != .add then gapError (.natOperator head.toString)
    let (pa, fa) ← reifyExpr a
    let (pb, fb) ← reifyExpr b
    pure (.seq pa pb, .bin op fa fb)

/-- Reify a shift whose operand type is `α`; the amount must be a literal. -/
partial def reifyShift (op : FBinop) (head : Name) (α a b : Expr) : ReifyM (FStmt × FExpr) := do
  match wordWidth? α with
  | none => gapError (.unsupportedType (toString (← ppExpr α)))
  | some _ =>
    if α.isConstOf ``Nat then gapError (.natOperator head.toString)
    match litValue? b with
    | none => gapError .shiftAmountNotLiteral
    | some n =>
      let (pa, fa) ← reifyExpr a
      pure (pa, .bin op fa (.lit n))

/-- Reify a boolean connective. -/
partial def reifyBool2 (op : FBinop) (a b : Expr) : ReifyM (FStmt × FExpr) := do
  let (pa, fa) ← reifyExpr a
  let (pb, fb) ← reifyExpr b
  pure (.seq pa pb, .bin op fa fb)

/-- Reify an application by its head constant. -/
partial def reifyApp (c : Name) (args : Array Expr) (e : Expr) : ReifyM (FStmt × FExpr) := do
  match c, args with
  | ``HAdd.hAdd, #[α, _, _, _, a, b] => reifyBin .add c α a b
  | ``HSub.hSub, #[α, _, _, _, a, b] => reifyBin .sub c α a b
  | ``HMul.hMul, #[α, _, _, _, a, b] => reifyBin .mul c α a b
  | ``HAnd.hAnd, #[α, _, _, _, a, b] => reifyBin .and c α a b
  | ``HOr.hOr, #[α, _, _, _, a, b] => reifyBin .or c α a b
  | ``HXor.hXor, #[α, _, _, _, a, b] => reifyBin .xor c α a b
  | ``HShiftLeft.hShiftLeft, #[α, _, _, _, a, b] => reifyShift .shl c α a b
  | ``HShiftRight.hShiftRight, #[α, _, _, _, a, b] => reifyShift .shr c α a b
  | ``and, #[a, b] => reifyBool2 .and a b
  | ``or, #[a, b] => reifyBool2 .or a b
  | ``xor, #[a, b] => reifyBool2 .xor a b
  | ``not, #[a] => do let (pa, fa) ← reifyExpr a; pure (pa, .not fa)
  | ``BEq.beq, #[_, _, a, b] => reifyBool2 .eq a b
  | ``bne, #[_, _, a, b] => do let (p, f) ← reifyBool2 .eq a b; pure (p, .not f)
  | ``Decidable.decide, #[p, _] => reifyProp p
  | ``Array.size, #[_, s] => do pure (.skip, .spanLen (← spanName s))
  | ``ByteArray.size, #[s] => do pure (.skip, .spanLen (← spanName s))
  | ``getElem!, _ => reifyGet args
  | ``ByteArray.get!, _ => reifyGet args
  | ``Option.isSome, #[_, o] => do pure (.skip, .bin .eq (.tagOf (← taggedName o)) (.lit 1))
  | ``Option.isNone, #[_, o] => do pure (.skip, .bin .eq (.tagOf (← taggedName o)) (.lit 0))
  | _, _ =>
      let _ := e
      gapError (.unknownHead c.toString)

/-- Reify an indexed read whose last two arguments are the span and the index. -/
partial def reifyGet (args : Array Expr) : ReifyM (FStmt × FExpr) := do
  if h : args.size ≥ 2 then
    let s := args[args.size - 2]
    let i := args[args.size - 1]
    let n ← spanName s
    let (pi, fi) ← reifyExpr i
    pure (pi, .spanGet n fi)
  else gapError (.unsupportedTerm "indexed read with fewer than two arguments")

/-- Reify a decidable proposition into a boolean expression; a `let`-bound
proposition is read as its boolean local. -/
partial def reifyProp (p : Expr) : ReifyM (FStmt × FExpr) := do
  let p := p.consumeMData.headBeta
  if p.isFVar then return ← reifyExpr p
  match p.getAppFnArgs with
  | (``Eq, #[.const ``Bool _, c, .const ``Bool.true _]) => reifyExpr c
  | (``Eq, #[_, a, b]) => reifyBool2 .eq a b
  | (``Ne, #[_, a, b]) => do let (s, f) ← reifyBool2 .eq a b; pure (s, .not f)
  | (``LT.lt, #[_, _, a, b]) => reifyBool2 .lt a b
  | (``LE.le, #[_, _, a, b]) => reifyBool2 .ule a b
  | (``GT.gt, #[_, _, a, b]) => reifyBool2 .lt b a
  | (``GE.ge, #[_, _, a, b]) => reifyBool2 .ule b a
  | (``And, #[a, b]) => do
      let (pa, fa) ← reifyProp a
      let (pb, fb) ← reifyProp b
      pure (.seq pa pb, .bin .and fa fb)
  | (``Or, #[a, b]) => do
      let (pa, fa) ← reifyProp a
      let (pb, fb) ← reifyProp b
      pure (.seq pa pb, .bin .or fa fb)
  | (``Not, #[a]) => do let (pa, fa) ← reifyProp a; pure (pa, .not fa)
  | (c, _) =>
      match p.getAppFn with
      | .const _ _ => gapError (.unknownHead c.toString)
      | _ => gapError (.unsupportedTerm (termKind p))

/-- Reify a `let x := v; b` into statements assigning `x` and then `target`. A
`let` of a decidable proposition becomes a boolean local. -/
partial def reifyLet (target : String) (n : Name) (ty v b : Expr) : ReifyM FStmt := do
  let isProp := ty.consumeMData.isProp
  let fty ← if isProp then pure FTy.bool else
    match ← leanTyToFTy ty with
    | some t => pure t
    | none => gapError (.letOfNonScalar n.eraseMacroScopes.toString (toString (← ppExpr ty)))
  unless fty.isScalar do
    gapError (.letOfNonScalar n.eraseMacroScopes.toString (toString (← ppExpr ty)))
  let name ← freshName n
  addLocal name fty
  let s1 ← if isProp then do
      let (pre, c) ← reifyProp v
      pure (FStmt.seq pre (.assign name c))
    else reifyStmt name v
  withLetDecl n ty v fun x => do
    let s2 ← withVar x.fvarId! (.var name) fty (reifyStmt target (b.instantiate1 x))
    pure (.seq s1 s2)

/-- Reify a bounded loop with a scalar accumulator into `assign target init`
followed by a `forLit` or `forLen`. `f` is the loop function of `arity`
binders, with the accumulator and index binders at `accPos` and `idxPos`. -/
partial def reifyLoop (target : String) (β f init bound : Expr)
    (accPos idxPos arity : Nat) : ReifyM FStmt := do
  let accTy ← match ← leanTyToFTy β with
    | some t => pure t
    | none => gapError (.letOfNonScalar target (toString (← ppExpr β)))
  unless accTy.isScalar do gapError (.letOfNonScalar target (toString (← ppExpr β)))
  let s0 ← reifyStmt target init
  let mk : String → FStmt → ReifyM FStmt ←
    if let some n := litValue? bound then
      pure fun i body => pure (.forLit i n body)
    else
      match bound.getAppFnArgs with
      | (``Array.size, #[_, s]) => do let sn ← spanName s; pure fun i body => pure (.forLen i sn body)
      | (``ByteArray.size, #[s]) => do let sn ← spanName s; pure fun i body => pure (.forLen i sn body)
      | _ => gapError .loopBoundNotStatic
  lambdaBoundedTelescope f arity fun xs body => do
    unless xs.size = arity do gapError (.unsupportedTerm "loop body that is not a lambda")
    let acc := xs[accPos]!
    let idx := xs[idxPos]!
    let iName ← freshName (← idx.fvarId!.getUserName)
    addLocal iName (.word .w64)
    let body' ← withVar acc.fvarId! (.var target) accTy <|
      withVar idx.fvarId! (.var iName) (.word .w64) <| reifyStmt target body
    let loop ← mk iName body'
    pure (.seq s0 loop)

/-- Reify `match o with | some v => a | none => b` on a tagged parameter, by
unfolding the matcher to `Option.casesOn`. -/
partial def reifyMatch (target : String) (e : Expr) : ReifyM FStmt := do
  let some e' ← delta? e | gapError .matchNotOnTagged
  let e' := e'.headBeta
  match e'.getAppFnArgs with
  | (``Option.casesOn, #[_, _, o, noneArm, someArm]) =>
      let s ← taggedName o
      let (_, payloadTy) ← match (← lookupVar o.fvarId!).2 with
        | .tagged tags w => pure (tags, FTy.word w)
        | _ => gapError .matchNotOnTagged
      let dflt ← reifyStmt target noneArm.headBeta
      let some ← lambdaBoundedTelescope someArm 1 fun xs body => do
        unless xs.size = 1 do gapError (.unsupportedTerm "match arm that is not a lambda")
        withVar xs[0]!.fvarId! (.payload s) payloadTy (reifyStmt target body)
      pure (.matchTag s [(1, some)] dflt)
  | _ => gapError .matchNotOnTagged

/-- Reify a body into statements that leave its value in `target`. -/
partial def reifyStmt (target : String) (e : Expr) : ReifyM FStmt := do
  let e := e.consumeMData.headBeta
  match e with
  | .letE n ty v b _ => reifyLet target n ty v b
  | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      match f with
      | .const c _ =>
          match c, args with
          | ``letFun, #[_, _, v, .lam n ty b _] => reifyLet target n ty v b
          | ``ite, #[_, p, _, t, el] =>
              let (pre, cnd) ← reifyProp p
              let st ← reifyStmt target t
              let se ← reifyStmt target el
              pure (.seq pre (.ite cnd st se))
          | ``cond, #[_, cnd, t, el] =>
              let (pre, c') ← reifyExpr cnd
              let st ← reifyStmt target t
              let se ← reifyStmt target el
              pure (.seq pre (.ite c' st se))
          | ``List.foldl, #[_, β, fn, init, l] =>
              match l.getAppFnArgs with
              | (``List.range, #[bound]) => reifyLoop target β fn init bound 0 1 2
              | _ => gapError .loopBoundNotStatic
          | ``Nat.fold, #[β, bound, fn, init] => reifyLoop target β fn init bound 2 0 3
          | ``Option.getD, #[_, o, d] =>
              let s ← taggedName o
              let sd ← reifyStmt target d
              pure (.ite (.bin .eq (.tagOf s) (.lit 1)) (.assign target (.payload s)) sd)
          | _, _ =>
              if (← getMatcherInfo? c).isSome then reifyMatch target e
              else
                let (pre, fe) ← reifyExpr e
                pure (.seq pre (.assign target fe))
      | _ => gapError (.unsupportedTerm (termKind e))
  | _ =>
      let (pre, fe) ← reifyExpr e
      pure (.seq pre (.assign target fe))

end

/-- Reify a Lean function into a fragment program. The function's parameters
become the program's parameters, its body is reified into statements that leave
the boolean result in the local `result`. -/
def reifyFragmentCore (e : Expr) : MetaM FProg := do
  let e ← instantiateMVars e
  let e ← whnf e
  lambdaTelescope e fun xs body => do
    let go : ReifyM FProg := do
      let mut params : Array (String × FTy) := #[]
      let mut env : ReifyEnv := []
      for x in xs do
        let decl ← x.fvarId!.getDecl
        let t ← leanTyToFTy! decl.type
        let name ← freshName decl.userName
        params := params.push (name, t)
        env := (x.fvarId!, (.var name, t)) :: env
      let resTy ← inferType body
      match ← leanTyToFTy resTy with
      | some .bool => pure ()
      | some t => gapError (.resultNotBool t)
      | none => gapError (.unsupportedType (toString (← ppExpr resTy)))
      let resName ← freshName `result
      addLocal resName .bool
      let stmt ← withReader (fun _ => env) (reifyStmt resName body)
      let st ← get
      pure { params := params.toList, locals := st.locals.toList, body := stmt,
             result := .var resName }
    (go.run []).run' {}

/-- `reifyFragment% f` is the `FProg` reified from the Lean function `f`. -/
elab "reifyFragment% " e:term : term => do
  let e' ← Term.elabTerm e none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e' ← instantiateMVars e'
  let p ← reifyFragmentCore e'
  pure (toExpr p)

end

end VerifiedEval

end
