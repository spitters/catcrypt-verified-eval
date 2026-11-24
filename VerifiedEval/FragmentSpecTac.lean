/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.FragmentSpec
public import VerifiedEval.FragmentNorm
public meta import VerifiedEval.FragmentNorm
public import VerifiedEval.FragmentReflect
public import Lean

/-!
# Producing the correctness theorem of a reified program

`fragment_theorem thm : f ~> p` states and proves that the fragment program `p` computes the
Lean function `f`:

```
thm : ∀ x₁ … xₙ, (admission hypotheses) → ∀ st, Agree L B st → p.run st = f x₁ … xₙ
```

where `L` and `B` bind the program's parameters to the encodings of `x₁ … xₙ` (`FEnc.enc`,
`encArr`, `encBytes`, `encOpt`), and the admission hypotheses bound every `Nat` parameter and
the size of every span parameter by `2 ^ 32`.

The proof is produced by translation validation along the structure of both sides: the walker
`solveSpec` reads the program statement and the source term of each judgment (`StmtTo`,
`ExprTo` of `VerifiedEval.FragmentSpec`) and applies the lemma for that construct, whose side
conditions (a name lookup, a width, a freshness test, a literal's encoding, a `Nat` bound) are
closed by `rfl`, `decide`, `omega` or an assumption. A `let`, a loop, a match and a hoisted
conditional each have their lemma; the program is not trusted, so a program that is not the
reification of `f` gets no theorem (the walker fails at the first construct that does not
match). The result is an ordinary proof term checked by the kernel: no axiom beyond those of
the lemmas, no `native_decide`.

Under `set_option profiler true` the walker reports its time by category: `fragment_theorem
unify` (the conclusion of a lemma against the goal), `fragment_theorem instances`,
`fragment_theorem prepGoal`, `fragment_theorem classify`, `fragment_theorem applyLemma` (the rest
of a lemma application) and one category per side-condition tactic (`fragment_theorem side rfl`,
`… decide`, `… omega`, `… assumption`), failed attempts included.

## Main definitions

* `solveSpec`: the walker.
* `fragment_theorem`: the command.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval.Spec

open Lean Meta Elab Term Command

meta section

/-- The lemmas tried on a `StmtTo` goal, in order. -/
def stmtLemmas : List Name :=
  [``StmtTo.skipSelf, ``StmtTo.ite, ``StmtTo.cond, ``StmtTo.foldlLit, ``StmtTo.foldlArr, ``StmtTo.foldlBytes,
   ``StmtTo.natFoldLit, ``StmtTo.natFoldArr, ``StmtTo.natFoldBytes, ``StmtTo.getD,
   ``StmtTo.matchSome, ``StmtTo.expr]

/-- The lemmas tried on an `ExprTo` goal, in order. -/
def exprLemmas : List Name :=
  [``ExprTo.lit, ``ExprTo.var, ``ExprTo.hoist,
   ``ExprTo.add, ``ExprTo.sub, ``ExprTo.mul, ``ExprTo.wand, ``ExprTo.wor, ``ExprTo.wxor,
   ``ExprTo.shl, ``ExprTo.shr, ``ExprTo.wbeq, ``ExprTo.wbne, ``ExprTo.wdeq, ``ExprTo.wne,
   ``ExprTo.wlt, ``ExprTo.wle, ``ExprTo.wgt, ``ExprTo.wge,
   ``ExprTo.nadd, ``ExprTo.nbeq, ``ExprTo.nbne, ``ExprTo.ndeq, ``ExprTo.nne, ``ExprTo.nlt,
   ``ExprTo.nle, ``ExprTo.ngt, ``ExprTo.nge,
   ``ExprTo.band, ``ExprTo.bor, ``ExprTo.bxor, ``ExprTo.bnot, ``ExprTo.bbeq, ``ExprTo.bbne, ``ExprTo.bdeq, ``ExprTo.bne',
   ``ExprTo.pand, ``ExprTo.por, ``ExprTo.pnot,
   ``ExprTo.sizeArr, ``ExprTo.sizeBytes, ``ExprTo.getArrU64, ``ExprTo.getArr, ``ExprTo.getBytes,
   ``ExprTo.isSome, ``ExprTo.isNone, ``ExprTo.payload, ``ExprTo.ptrue]

/-- The tactics that close side conditions, tried in order, each with its profiler category
(`set_option profiler true` reports the time spent in each, failed attempts included). -/
def sideTactics : MetaM (List (String × Syntax.Tactic)) := do
  pure [("fragment_theorem side rfl", ← `(tactic| rfl)),
    ("fragment_theorem side decide", ← `(tactic| decide)),
    ("fragment_theorem side omega", ← `(tactic| omega)),
    ("fragment_theorem side assumption", ← `(tactic| assumption)),
    ("fragment_theorem side omega", ← `(tactic| (simp only [ByteArray.size] at *; omega)))]

/-- Close a side condition: a lookup, a width, a freshness test, a literal's encoding, a bound. -/
def solveSide (g : MVarId) : TermElabM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let opts ← getOptions
  let mut closed := false
  for (cat, tac) in ← sideTactics do
    unless closed do
      let s ← saveState
      let r ← profileitM Exception cat opts do
        try
          let gs ← Tactic.run g (Tactic.evalTactic tac)
          pure gs.isEmpty
        catch _ => pure false
      if r then closed := true else s.restore
  unless closed do
    throwError "fragment_theorem: side condition not closed{indentExpr ty}\n{MessageData.ofGoal g}"

/-- Whether a goal is one of the two judgments. -/
def judgmentHead? (ty : Expr) : Option Name :=
  match ty.getAppFn.constName? with
  | some ``StmtTo => some ``StmtTo
  | some ``ExprTo => some ``ExprTo
  | _ => none

/-- The tag of the error of a lemma whose conclusion does not unify with the goal: the walker
moves to the next lemma without recording it, and recognises it by the tag, without formatting
the message (formatting the failed attempts took most of the walker's time, see the report of
VE-REIFY). -/
def noApplyTag : Name := `fragment_theorem.noApply

/-- Apply `lem` to `g`, with the arguments named in `pre` fixed first. Returns the remaining
hypotheses in binder order, the instance arguments synthesized. -/
def applyLemma (g : MVarId) (lem : Name) (pre : List (Name × Expr) := []) :
    MetaM (List MVarId) := do
  let c ← mkConstWithFreshMVarLevels lem
  let cty ← inferType c
  let (ms, bis, concl) ← forallMetaTelescope cty
  let names ← forallTelescope cty fun xs _ => xs.mapM fun x => x.fvarId!.getUserName
  for (n, v) in pre do
    match names.findIdx? (· == n) with
    | some i => unless ← isDefEq ms[i]! v do throwError "fragment_theorem: {lem}: {n} mismatch"
    | none => throwError "fragment_theorem: {lem} has no argument {n}"
  -- the match of the conclusion unfolds instances only: the program is in constructor form
  -- and the source value is matched up to instances, so a mismatch fails at once
  let gty ← g.getType
  unless ← profileitM Exception "fragment_theorem unify" (← getOptions)
      (withTransparency .instances (isDefEq concl gty)) do
    throwError (.tagged noApplyTag
      m!"fragment_theorem: {lem} does not apply{indentExpr concl}\nvs{indentExpr (← g.getType)}")
  for i in [:ms.size] do
    if bis[i]! == .instImplicit then
      let m := ms[i]!
      let ty ← instantiateMVars (← inferType m)
      let inst ← profileitM Exception "fragment_theorem instances" (← getOptions) (synthInstance ty)
      unless ← isDefEq m inst do throwError "fragment_theorem: {lem}: instance mismatch"
  g.assign (mkAppN c ms)
  let mut out := #[]
  for i in [:ms.size] do
    if bis[i]! != .instImplicit then out := out.push ms[i]!.mvarId!
  return out.toList

/-- The source value `e` of a judgment whose value argument is `enc e`. -/
def valueOf? (ty : Expr) : Option Expr :=
  let args := ty.getAppArgs
  if args.size ≥ 6 then
    let v := args[5]!
    if v.isAppOfArity ``FEnc.enc 3 then some v.appArg! else none
  else none

/-- Replace the source value of a judgment. -/
def withValue (ty : Expr) (e : Expr) : Expr :=
  let args := ty.getAppArgs
  let v := args[5]!
  mkAppN ty.getAppFn (args.set! 5 (mkApp v.appFn! e))

/-- Normalise a goal: instantiate, beta-reduce, unfold a matcher at the head of the value. -/
def prepGoal (g : MVarId) : MetaM MVarId := do
  let ty ← instantiateMVars (← g.getType)
  let ty ← Core.betaReduce ty
  let ty ← match valueOf? ty with
    | some e =>
      match e.getAppFn.constName? with
      | some c =>
        if (← getMatcherInfo? c).isSome then
          match ← delta? e with
          | some e' => pure (withValue ty e'.headBeta)
          | none => pure ty
        else pure ty
      | none => pure ty
    | none => pure ty
  g.replaceTargetDefEq ty

mutual

/-- Prove a judgment, a side condition, or a universally quantified judgment (a loop body). -/
partial def solveSpec (g : MVarId) : TermElabM Unit := g.withContext do
  if ← g.isAssigned then return
  let g ← profileitM Exception "fragment_theorem prepGoal" (← getOptions) (prepGoal g)
  let ty ← g.getType
  if ty.isForall then
    let (_, g') ← g.intros
    return ← solveSpec g'
  match judgmentHead? ty with
  | some h => solveJudgment g h
  | none => solveSide g

/-- Try the lemmas of a judgment in order; commit to the first whose conclusion unifies and
whose side conditions close, then prove its judgments. -/
partial def solveJudgment (g : MVarId) (head : Name) : TermElabM Unit := g.withContext do
  let ty ← g.getType
  -- a `let` in the source value: the `let` lemma with the bound value and the body fixed
  if head == ``StmtTo then
    if let some (.letE n t v b _) := valueOf? ty then
      -- the body with the bound value substituted: a `let` whose body is typed only by
      -- unfolding the bound name (an instance found through it) stays well typed
      let lam := Expr.lam n t (b.instantiate1 v) .default
      if t.isProp then
        let gs ← applyLemma g ``StmtTo.letProp [(`p, v), (`b, lam)]
        return ← finish gs
      let gs ← applyLemma g ``StmtTo.letE [(`a, v), (`b, lam)]
      return ← finish gs
  -- a conversion in the source value is the identity on the word: its lemma goes first, so
  -- that no other lemma compares the converted value with a binding
  if head == ``ExprTo then
    if let some e := valueOf? ty then
      if e.isAppOfArity ``Nat.toUInt64 1 then
        return ← finish (← applyLemma g ``ExprTo.ofNat64)
      if e.isAppOfArity ``UInt64.toNat 1 then
        return ← finish (← applyLemma g ``ExprTo.toNat64)
      -- `decide (c = true)` is reified as `c` itself
      if e.isAppOfArity ``Decidable.decide 2 then
        let p := e.appFn!.appArg!
        if p.isAppOfArity ``Eq 3 && p.appArg!.isConstOf ``Bool.true then
          return ← finish (← applyLemma g ``ExprTo.ptrue)
  let lemmas := if head == ``StmtTo then stmtLemmas else exprLemmas
  let mut lastErr : MessageData := m!"no lemma applies"
  for lem in lemmas do
    let s ← saveState
    let r ← try
        let gs ← profileitM Exception "fragment_theorem applyLemma" (← getOptions) (applyLemma g lem)
        -- side conditions first: a failure here selects the next lemma
        let mut judg := #[]
        for g' in gs do
          if ← g'.isAssigned then continue
          let t ← instantiateMVars (← g'.getType)
          let isJ ← profileitM Exception "fragment_theorem classify" (← getOptions) do
            pure ((judgmentHead? (← whnfR t)).isSome || t.isForall || t.hasExprMVar)
          if (← isProp t) then
            if isJ then
              judg := judg.push g'
            else solveSide g'
          else judg := judg.push g'
        pure (some judg.toList)
      catch e =>
        unless e.toMessageData.hasTag (· == noApplyTag) do
          lastErr := m!"{lem}: {e.toMessageData}"
        s.restore
        pure none
    -- committed: the construct matches, a failure below is final
    if let some judg := r then return ← finish judg
  throwError "fragment_theorem: no construct lemma proves{indentExpr ty}\nlast failure: {lastErr}"

/-- Prove the judgments of an applied lemma in order. -/
partial def finish (gs : List MVarId) : TermElabM Unit := do
  for g' in gs do
    if ← g'.isAssigned then continue
    let t ← instantiateMVars (← g'.getType)
    if ← isProp t then solveSpec g'
  for g' in gs do
    unless ← g'.isAssigned do
      throwError "fragment_theorem: an argument was left undetermined"

end

/-- The elements of a list literal. -/
partial def listElems (e : Expr) : MetaM (List Expr) := do
  let e ← whnf e
  if e.isAppOfArity ``List.cons 3 then return e.appFn!.appArg! :: (← listElems e.appArg!)
  if e.isAppOfArity ``List.nil 1 then return []
  throwError "fragment_theorem: not a list literal{indentExpr e}"

/-- The string of a string literal. -/
def strOf (e : Expr) : MetaM String := do
  match (← whnf e) with
  | .lit (.strVal s) => pure s
  | e => throwError "fragment_theorem: not a string literal{indentExpr e}"

/-- How a parameter is bound: a scalar binding, or a buffer binding by its encoding. -/
inductive ParamKind
  | scalar | nat | arr | bytes | opt

/-- The kind of a parameter of the given Lean type. -/
def paramKind (ty : Expr) : MetaM ParamKind := do
  let ty ← whnfR ty
  match ty with
  | .const ``UInt8 _ | .const ``UInt16 _ | .const ``UInt32 _ | .const ``UInt64 _
  | .const ``Bool _ => pure .scalar
  | .const ``Nat _ => pure .nat
  | .const ``ByteArray _ => pure .bytes
  | .app (.const ``Array _) _ => pure .arr
  | .app (.const ``Option _) _ => pure .opt
  | _ => throwError "fragment_theorem: parameter type {ty} has no encoding"

/-- The constructor normal form of a closed term: the program as the walker reads it. -/
partial def normConstr (e : Expr) : MetaM Expr := do
  let e ← whnf e
  match e with
  | .lit _ => pure e
  | _ =>
    if e.getAppFn.isConst then
      let args ← e.getAppArgs.mapM normConstr
      pure (mkAppN e.getAppFn args)
    else pure e

/-- The statement and proof of the correctness theorem of `p` for `f`. -/
def mkFragmentTheorem (f p : Expr) : TermElabM (Expr × Expr) := do
  let pv ← normConstr p
  unless pv.isAppOfArity ``FProg.mk 4 do throwError "fragment_theorem: {p} is not a program"
  let params ← listElems (pv.getArg! 0)
  let body := pv.getArg! 2
  let res := pv.getArg! 3
  let res ← whnf res
  unless res.isAppOfArity ``FExpr.var 1 do throwError "fragment_theorem: the result is not a local"
  let r ← strOf res.appArg!
  let names ← params.mapM fun q => do
    let q ← whnf q
    strOf (q.getArg! 2)
  let fty ← inferType f
  forallTelescopeReducing fty fun xs _ => do
    unless xs.size == names.length do
      throwError "fragment_theorem: {xs.size} arguments against {names.length} parameters"
    let sEnvTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkApp (mkConst ``BitVec) (mkNatLit 64))
    let bEnvTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String)
      (mkApp (mkConst ``List [0]) (mkApp (mkConst ``BitVec) (mkNatLit 64)))
    let mut lEnts : Array Expr := #[]
    let mut bEnts : Array Expr := #[]
    let mut adms : Array (Name × Expr) := #[]
    for x in xs, n in names do
      let xty ← inferType x
      let nm := mkStrLit n
      match ← paramKind xty with
      | .scalar => lEnts := lEnts.push (← mkAppM ``Prod.mk #[nm, ← mkAppM ``FEnc.enc #[x]])
      | .nat =>
        lEnts := lEnts.push (← mkAppM ``Prod.mk #[nm, ← mkAppM ``FEnc.enc #[x]])
        adms := adms.push (.mkSimple s!"h_{n}", ← mkAppM ``LT.lt #[x, mkNatLit (2 ^ 32)])
      | .arr =>
        bEnts := bEnts.push (← mkAppM ``Prod.mk #[nm, ← mkAppM ``encArr #[x]])
        adms := adms.push (.mkSimple s!"h_{n}",
          ← mkAppM ``LT.lt #[← mkAppM ``Array.size #[x], mkNatLit (2 ^ 32)])
      | .bytes =>
        bEnts := bEnts.push (← mkAppM ``Prod.mk #[nm, ← mkAppM ``encBytes #[x]])
        adms := adms.push (.mkSimple s!"h_{n}",
          ← mkAppM ``LT.lt #[← mkAppM ``ByteArray.size #[x], mkNatLit (2 ^ 32)])
      | .opt => bEnts := bEnts.push (← mkAppM ``Prod.mk #[nm, ← mkAppM ``encOpt #[x]])
    let L ← mkListLit sEnvTy lEnts.toList
    let B ← mkListLit bEnvTy bEnts.toList
    let fx := mkAppN f xs
    withLocalDeclsDND adms fun hs => do
      let st ← mkFreshUserName `st
      withLocalDeclD st (mkConst ``FState) fun stx => do
        let hstTy ← mkAppM ``Agree #[L, B, stx]
        withLocalDeclD `hst hstTy fun hst => do
          let concl ← mkEq (← mkAppM ``FProg.run #[p, stx]) fx
          -- the judgment on the body, with the source function unfolded
          let fBody ← match ← delta? fx with
            | some e => pure e.headBeta
            | none => pure fx
          let encRes ← mkAppM ``FEnc.enc #[fBody]
          let widths ← mkAppM ``FProg.widths #[p]
          let judgTy := mkAppN (mkConst ``StmtTo) #[widths, L, B, body, mkStrLit r, encRes]
          let g ← mkFreshExprMVar judgTy
          solveSpec g.mvarId!
          let hr ← mkEqRefl res
          let pf ← mkAppOptM ``StmtTo.run #[p, L, B, mkStrLit r, fx, hr, ← instantiateMVars g]
          let pf := mkApp2 pf stx hst
          let thmTy ← mkForallFVars (xs ++ hs ++ #[stx, hst]) concl
          let thmPf ← mkLambdaFVars (xs ++ hs ++ #[stx, hst]) pf
          return (thmTy, ← instantiateMVars thmPf)

/-- The statement and proof of the correctness theorem of a program `p` not in the reifier's
shape (a hand-written program), by normalisation: `f` is reified with `p`'s result name into
`q`, the walker proves the judgment about `q`'s body under `p`'s widths, and `run_ofNorm`
transfers it to `p` when the normal form of `q`'s body, after `k` leading literal
assignments are stripped, is that of `p`'s body. The theorem then also assumes that the state
holds the stripped values (`Holds`). Admission hypotheses the proof does not use are dropped. -/
def mkFragmentTheoremNorm (f p : Expr) : TermElabM (Expr × Expr) := do
  let pv ← normConstr p
  unless pv.isAppOfArity ``FProg.mk 4 do throwError "fragment_theorem: {p} is not a program"
  let params ← listElems (pv.getArg! 0)
  let res ← whnf (pv.getArg! 3)
  unless res.isAppOfArity ``FExpr.var 1 do throwError "fragment_theorem: the result is not a local"
  let r ← strOf res.appArg!
  let names ← params.mapM fun q => do
    let q ← whnf q
    strOf (q.getArg! 2)
  let qv ← reifyFragmentCore f (.mkSimple r)
  unless qv.params.map (·.1) == names do
    throwError "fragment_theorem: the source's parameters {qv.params.map (·.1)} are not the program's {names}"
  let qn := qv.body.norm
  let pn ← normConstr (mkApp (mkConst ``FStmt.norm) (pv.getArg! 2))
  let mut kOpt : Option Nat := none
  for k in [0:qn.countInits + 1] do
    if kOpt.isNone then
      if (← normConstr (toExpr (FStmt.stripInits k qn).2)) == pn then kOpt := some k
  let some k := kOpt
    | throwError "fragment_theorem: the normal form of the reified source is not that of the program{indentExpr (toExpr qn)}\nvs{indentExpr pn}"
  let inits := (FStmt.stripInits k qn).1
  let qE ← normConstr (toExpr qv.body)
  let fty ← inferType f
  forallTelescopeReducing fty fun xs _ => do
    unless xs.size == names.length do
      throwError "fragment_theorem: {xs.size} arguments against {names.length} parameters"
    let sEnvTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkApp (mkConst ``BitVec) (mkNatLit 64))
    let bEnvTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String)
      (mkApp (mkConst ``List [0]) (mkApp (mkConst ``BitVec) (mkNatLit 64)))
    let mut lEnts : Array Expr := #[]
    let mut bEnts : Array Expr := #[]
    let mut adms : Array (Name × Expr) := #[]
    for x in xs, n in names do
      let xty ← inferType x
      let nm := mkStrLit n
      match ← paramKind xty with
      | .scalar => lEnts := lEnts.push (← mkAppM ``Prod.mk #[nm, ← mkAppM ``FEnc.enc #[x]])
      | .nat =>
        lEnts := lEnts.push (← mkAppM ``Prod.mk #[nm, ← mkAppM ``FEnc.enc #[x]])
        adms := adms.push (.mkSimple s!"h_{n}", ← mkAppM ``LT.lt #[x, mkNatLit (2 ^ 32)])
      | .arr =>
        bEnts := bEnts.push (← mkAppM ``Prod.mk #[nm, ← mkAppM ``encArr #[x]])
        adms := adms.push (.mkSimple s!"h_{n}",
          ← mkAppM ``LT.lt #[← mkAppM ``Array.size #[x], mkNatLit (2 ^ 32)])
      | .bytes =>
        bEnts := bEnts.push (← mkAppM ``Prod.mk #[nm, ← mkAppM ``encBytes #[x]])
        adms := adms.push (.mkSimple s!"h_{n}",
          ← mkAppM ``LT.lt #[← mkAppM ``ByteArray.size #[x], mkNatLit (2 ^ 32)])
      | .opt => bEnts := bEnts.push (← mkAppM ``Prod.mk #[nm, ← mkAppM ``encOpt #[x]])
    let L ← mkListLit sEnvTy lEnts.toList
    let B ← mkListLit bEnvTy bEnts.toList
    let fx := mkAppN f xs
    withLocalDeclsDND adms fun hs => do
      let st ← mkFreshUserName `st
      withLocalDeclD st (mkConst ``FState) fun stx => do
        let hstTy ← mkAppM ``Agree #[L, B, stx]
        withLocalDeclD `hst hstTy fun hst => do
          let IE := toExpr inits
          let hhTy ← mkAppM ``Holds #[IE, stx]
          withLocalDeclD `hinit hhTy fun hh => do
            let concl ← mkEq (← mkAppM ``FProg.run #[p, stx]) fx
            let fBody ← match ← delta? fx with
              | some e => pure e.headBeta
              | none => pure fx
            let encRes ← mkAppM ``FEnc.enc #[fBody]
            let widths ← mkAppM ``FProg.widths #[p]
            let judgTy := mkAppN (mkConst ``StmtTo) #[widths, L, B, qE, mkStrLit r, encRes]
            let g ← mkFreshExprMVar judgTy
            solveSpec g.mvarId!
            let kE := mkNatLit k
            let hr ← mkEqRefl res
            let normP := mkApp (mkConst ``FStmt.norm) (← mkAppM ``FProg.body #[p])
            let hn ← mkEqRefl normP
            let fitsTy := mkApp2 (mkConst ``Fits) widths IE
            let hf ← mkDecideProof fitsTy
            unless ← isDefEq (← inferType hf) fitsTy do
              throwError "fragment_theorem: a stripped literal does not fit its width"
            let pf := mkAppN (mkConst ``run_ofNorm)
              #[p, L, B, mkStrLit r, fx, qE, kE, hr, ← instantiateMVars g, hn, hf, stx, hst]
            let (extra, pf) :=
              if inits.isEmpty then (#[], mkApp pf (mkApp (mkConst ``Holds.nil) stx))
              else (#[hh], mkApp pf hh)
            let pf ← instantiateMVars pf
            let hsUsed := hs.filter fun h => pf.containsFVar h.fvarId!
            let thmTy ← mkForallFVars (xs ++ hsUsed ++ #[stx, hst] ++ extra) concl
            let thmPf ← mkLambdaFVars (xs ++ hsUsed ++ #[stx, hst] ++ extra) pf
            return (thmTy, ← instantiateMVars thmPf)

/-- The correctness theorem of `p` for `f`: by the walker on `p` itself when `p` is in the
reifier's shape, otherwise by normalisation (`mkFragmentTheoremNorm`). -/
def mkFragmentTheoremAny (f p : Expr) : TermElabM (Expr × Expr) := do
  let s ← saveState
  try mkFragmentTheorem f p
  catch e1 =>
    s.restore
    try mkFragmentTheoremNorm f p
    catch e2 =>
      throwError "{e1.toMessageData}\nby normalisation: {e2.toMessageData}"

/-- `fragment_theorem thm : f ~> p` adds the theorem `thm` that the program `p` computes `f` on
every state agreeing with the encodings of the arguments (`mkFragmentTheorem`). -/
elab "fragment_theorem " n:ident " : " f:term " ~> " p:term : command => do
  let declName := (← getCurrNamespace) ++ n.getId
  liftTermElabM do
    let fe ← Term.elabTerm f none
    let pe ← Term.elabTerm p (some (mkConst ``FProg))
    Term.synthesizeSyntheticMVarsNoPostponing
    let fe ← instantiateMVars fe
    let pe ← instantiateMVars pe
    let (ty, pf) ← mkFragmentTheoremAny fe pe
    addDecl (.thmDecl { name := declName, levelParams := [], type := ty, value := pf })

/-- `fragment_theorem_rejects f ~> p` succeeds when `fragment_theorem` produces no theorem for
`p` and `f`, and reports the construct at which the walker stopped; it is an error when a
theorem is produced. The negative tests use it. -/
elab "fragment_theorem_rejects " f:term " ~> " p:term : command => do
  liftTermElabM do
    let fe ← Term.elabTerm f none
    let pe ← Term.elabTerm p (some (mkConst ``FProg))
    Term.synthesizeSyntheticMVarsNoPostponing
    let fe ← instantiateMVars fe
    let pe ← instantiateMVars pe
    let s ← saveState
    let r ← try
        let _ ← mkFragmentTheoremAny fe pe
        pure none
      catch e => pure (some (← e.toMessageData.toString))
    s.restore
    match r with
    | none => throwError "fragment_theorem_rejects: a theorem was produced"
    | some msg =>
      let lines := msg.splitOn "\n"
      let i := (lines.findIdx? (fun l => (l.splitOn "last failure").length > 1)).getD 0
      let last := (lines.drop i).take 2 |>.map (·.trimAscii.toString)
      logInfo m!"no theorem; {" ".intercalate last}"

end

end VerifiedEval.Spec

end
