import Lean
import Lean4Axiomatic.Relation.Equivalence
import Mathlib.Tactic.GCongr

namespace Lean4Axiomatic.Tactic

/-!
# Tactics for term rewriting

The tactics in this file are useful for proving "rewrites", or substitutions,
where a subexpression of a term is replaced by another (related) subexpression.
They are heavily copied from Mathlib's `gcongr` and `grw` tactics and still use
parts of the supporting machinery, most notably the `gcongr` annotations for
congruence lemmas. However, the code has been dramatically simplified to only
support features needed by this project.
-/

open Lean (Expr MVarId Name Syntax getExprMVarAssignment? mkAppN)
open Lean.Elab.Tactic (Tactic TacticM elabTerm getMainGoal)
open Lean.Meta (
  MetaM isDefEq inferType isProof kabstract mkAppM mkConstWithFreshMVarLevels
  mkFreshExprMVar saveState whnf withReducible withReducibleAndInstances
)
open Lean.MVarId (gcongrForward)
open Lean.Parser.Tactic (rwRuleSeq)
open Mathlib.Tactic.GCongr (gcongrExt gcongrForwardDischarger GCongrKey)
open Mathlib.Tactic.GCongr renaming getRel → parseGCongrRel

/--
Retrieve a metavariable's type with some additional processing to bring it into
a useful form for tactics.
-/
private def mvarType (mvarId : MVarId) : MetaM Expr :=
  /-
  Instantiate metavariables, but only minimally reduce, to prevent large
  changes in the type's shape.
  -/
  withReducible mvarId.getType'

/--
When the given expression is a named constant applied to any number of
arguments (including zero), return the name and all arguments in order.

Expands local `let` declarations and evaluates lambda applications for
convenience.
-/
private partial def parseFnAndArgs
    (e : Expr) : MetaM (String ⊕ (Name × Array Expr))
    :=
  aux e #[]
where
  aux : Expr → Array Expr → MetaM (String ⊕ (Name × Array Expr))
  | .const n .., args =>
    return .inr (n, args)
  | .fvar fvid, args => do
    let some value ← fvid.getValue? |
      return .inl s!"local var [{fvid.name}] missing value"
    aux value args
  | e@(.lam ..), args =>
    -- Only beta-reduce lambda applications, else we might expand too many defs
    let reducedExprAndArgs := e.beta args
    parseFnAndArgs reducedExprAndArgs
  | e, outerArgs =>
    e.withApp λ fnExpr args => do
      -- `e` wasn't a function application
      if args.isEmpty then return .inl s!"expr [{fnExpr}] isn't a fn app"

      -- Continue trying to extract args from `fnExpr`
      aux fnExpr (args ++ outerArgs)

private def gcongrKeyToString (key : GCongrKey) : String :=
  s!"\{relName={key.relName}, head={key.head}, arity={key.arity}}"

instance gcongr_key_to_string_inst : ToString GCongrKey := {
  toString := gcongrKeyToString
}

/--
Solve a goal via a congruence argument: show that the goal's type follows from
the provided rewrite rule's type by "doing the same thing to both sides".

The goal's type must be of the form `tL ~ tR`, where `~` is a binary relation
and `tL`, `tR` are terms. The rewrite rule's type must similarly be of the form
`sL ≈ sR`, where `≈` is a binary relation (possibly the same as `~`) and `sL`,
`sR` are terms. The term `tL` must contain one or more occurrences of `sL` as a
subterm, and the same must hold for `tR` and `sR`. In addition, the only
difference between `tL` and `tR` is that `tL` contains `sL` in exactly the
places where `tR` contains `sR`; in other words, there is some function `f`
such that the goal's type has the form `f sL ~ f sR`.

This tactic applies theorems with `gcongr` annotations to the goal, recursively
reducing it to simpler relational expressions until the rewrite rule can solve
it directly. Thus, the tactic will fail if a relevant theorem is not annotated.
Some auxiliary goals may be generated from this process, but if they all have
exact matches in the surrounding proof context then the tactic will close them
automatically.

No attempt is made to unwind changes to the proof context on failure, and any
unsolved goals will "leak" into the top-level definition's context.
-/
private partial def simpleCongruence
    (goal : MVarId) (rwRule : Expr) : TacticM Unit
    := goal.withContext do
  /- Base case: can we easily close the goal? -/
  if ← goal.gcongrForward #[rwRule] then return ()

  /- Find the theorems with `gcongr` attribute that may apply to the goal. -/
  let candidateLemmas ← do
    let goalType ← mvarType goal
    let some (goalRelName, lhs, rhs) := parseGCongrRel goalType
      | throwError "goal type [{goalType}] is not an applied binary relation"

    /- LHS and RHS must have the same form: `f x₁ ... xₙ ~ f y₁ ... yₙ`. -/
    let lhsFnRes ← parseFnAndArgs lhs.cleanupAnnotations
    let (lhsFnName, lhsArgs) ← match lhsFnRes with
    | .inr (name, args) => pure (name, args)
    | .inl errMsg => throwError "LHS [{lhs}] parse err: {errMsg}"
    let rhsFnRes ← parseFnAndArgs rhs.cleanupAnnotations
    let (rhsFnName, rhsArgs) ← match rhsFnRes with
    | .inr (name, args) => pure (name, args)
    | .inl errMsg => throwError "RHS [{rhs}] parse err: {errMsg}"
    unless lhsFnName == rhsFnName do
      throwError "LHS fn [{lhsFnName}] != RHS fn [{rhsFnName}]"
    unless lhsArgs.size == rhsArgs.size do
      throwError "LHS arity {lhsArgs.size} != RHS arity {rhsArgs.size}"

    /-
    Detect whether the arguments on the LHS vs. RHS of the goal are "different"
    or not, where "different" has a specific meaning set by
    `Mathlib.Tactic.GCongr.makeGCongrLemma`.
    -/
    let varyingArgs ← withReducibleAndInstances $
      (lhsArgs.zip rhsArgs).mapM λ (lhsArg, rhsArg) => do
        let argsEq ← isDefEq lhsArg rhsArg
        let isSame := argsEq || (← isProof lhsArg) && (← isProof rhsArg)
        pure !isSame
    if varyingArgs.all not then
      throwError "fn args on LHS and RHS are all the same; no work to do"

    /- Look up relevant `gcongr` definitions using goal data extracted above. -/
    let key :=
      { relName := goalRelName, head := lhsFnName, arity := lhsArgs.size }
    let gcongrLemmasMap := gcongrExt.getState (← Lean.MonadEnv.getEnv)
    let lemmas := gcongrLemmasMap.getD key []
    if lemmas.isEmpty then throwError "no lemmas for key: {key}"
    pure lemmas

  /- Commit to the first candidate that closes the goal. -/
  let successfulLemmaDataOpt ← withReducibleAndInstances do
    let checkpoint ← saveState
    for gcongrLemma in candidateLemmas do
      try
        let lemmaNameExpr ← mkConstWithFreshMVarLevels gcongrLemma.declName
        let subgoals ← goal.apply lemmaNameExpr
        return some (gcongrLemma, subgoals)
      catch _ =>
        checkpoint.restore
    return none
  let some (gcongrLemma, subgoals) := successfulLemmaDataOpt
    | throwError
        "no applicable gcongr lemmas among {candidateLemmas.length} candidates"

  /-
  Recursively apply this tactic to the chosen lemma's hypotheses of the form
  `x₁ ≈ x₂` whose terms appear in the goal type as `f .. x₁ .. ~ f .. x₂ ..`.
  -/
  let some goalExpr ← getExprMVarAssignment? goal | panic! "goal not assigned"
  let goalArgs := goalExpr.getAppArgs
  for (i, _, _) in gcongrLemma.mainSubgoals do
    let some (.mvar mainSubgoal) := goalArgs[i]? | panic! "bad subgoal index"
    simpleCongruence mainSubgoal rwRule

  /- Try to solve the remaining subgoals of the chosen lemma. -/
  for subgoal in subgoals do
    if (← subgoal.isAssigned) then continue
    let checkpoint ← saveState
    -- These goals tend to be simple `Prop`s, already in the local context.
    try subgoal.assumption
    catch _ => checkpoint.restore

/-- Undo `parseGCongrRel`: apply the named relation to the given terms. -/
private def mkAppRel (relName : Name) (lhs rhs : Expr) : MetaM Expr :=
  if relName = `_Implies then return .forallE `x lhs rhs .default
  else mkAppM relName #[lhs, rhs]

/--
Prove a "simple congruence" for each given rule, to solve the goal.

The rules array is assumed to have been produced by `rwRuleSeqElab`. Fails if
the array is empty, or if a congruence proof fails for any of the rules.
-/
private def simpleRewrite
    (initialGoal : MVarId) (directedRules : Array Expr) : TacticM Unit
    := do
  /-
  Handle the last rule as a special case, for these benefits:
  1. Directly solves the final goal, skipping one iteration of between-rule
     processing that would otherwise happen with a uniform approach. This also
     avoids needing to solve the trivial reflexivity that would be the final
     goal in that situation.
  2. Most usages of this tactic will only have one rule, so this approach
     highlights the common case.
  3. Provides a natural way to fail fast if no rules were provided.
  -/
  let some finalRule := directedRules.back? | throwError "no rw rules given"

  /- Prepare for iteration over the other rules. -/
  let mut remainingGoal := initialGoal
  let earlierRules := directedRules.pop
  unless earlierRules.isEmpty do
    /-
    We require the goal type to have the form `lhs ~ rhs`, where `~` is a
    binary relation (e.g. `≃` or `≤`) and `lhs`, `rhs` are its child terms.
    -/
    let initialGoalType ← mvarType initialGoal
    let errExplanation := "is not an applied binary relation"
    let some (relInit, lhsInit, rhsInit) := parseGCongrRel initialGoalType
      | throwError "initial goal type [{initialGoalType}] {errExplanation}"
    let applyRelInit : Expr → Expr → MetaM Expr :=
      if relInit = `_Implies then (return .forallE `x · · .default)
      else (mkAppM relInit #[·, ·])

    /- Update the goal after rewriting with each rule except the last. -/
    let mut lhsCurr := lhsInit
    for rwRule in earlierRules do
      /-
      We also require each rule's type to be of the form `lhs ≈ rhs`, but we
      don't care what the relation is; that'll be checked when the proof term
      for the rewrite is built.
      -/
      let rwRuleType ← inferType rwRule
      let some (_, lhsRule, rhsRule) := parseGCongrRel rwRuleType
        | throwError "rewrite rule type [{rwRuleType}] {errExplanation}"

      /- Replace the rule's LHS with its RHS, everywhere in the goal's LHS. -/
      if lhsRule.isMVar then throwError "lhs of rule is mvar, cannot abstract"
      let lhsCurrAbs ← kabstract lhsCurr lhsRule
      let lhsCurrRw := lhsCurrAbs.instantiate1 rhsRule

      /- Prove the rule's rewrite. -/
      let rwSubgoalType ← applyRelInit lhsCurr lhsCurrRw
      let rwSubgoal ← mkFreshExprMVar rwSubgoalType
      simpleCongruence rwSubgoal.mvarId! rwRule

      /- Replace the goal with a smaller one for the next iteration. -/
      let nextSubgoalType ← applyRelInit lhsCurrRw rhsInit
      let nextSubgoal ← mkFreshExprMVar nextSubgoalType
      let remainingGoalProof ← mkAppM ``Trans.trans #[rwSubgoal, nextSubgoal]
      remainingGoal.assign remainingGoalProof
      remainingGoal := nextSubgoal.mvarId!
      lhsCurr := lhsCurrRw

  simpleCongruence remainingGoal finalRule

/--
Core of the "predicate rewrite" tactic.

Given a goal metavariable of type `β`, and a function argument term of type `α`,
attempts to construct a function term of type `α → β` using the provided rewrite
rules and, if successful, assigns to the goal the result of calling the function
on the argument.

Callers should ensure that they're using the goal's metavariable context before
invoking this function.
-/
private def predicateRewrite
    (goal : MVarId) (directedRules : Array Expr) (fnArg : Expr) : TacticM Unit
    := do
  /-
  Create a subgoal metavariable for the function term we want to generate. We
  must give it an explicit type: Lean isn't able to infer it.
  -/
  let fnArgType ← inferType fnArg
  let goalType ← goal.getType
  let fnGoalType := .forallE `x fnArgType goalType .default
  let fn ← mkFreshExprMVar (some fnGoalType)

  /- We can now solve the main goal, and delegate the function subgoal. -/
  goal.assign (.app fn fnArg)
  simpleRewrite (initialGoal := fn.mvarId!) directedRules

/-- Perform elaboration on syntax matching `Lean.Parser.Category.term`. -/
private def termElab (termStx : Syntax) : TacticM Expr := do
  -- Requiring metavariable resolution here causes failures
  let term ← elabTerm termStx (expectedType? := none) (mayPostpone := true)
  -- Elaboration failed; we need to give up to prevent subtle errors downstream
  if term.hasSyntheticSorry then throwError "term did not elab: {term}"
  return term

/-- Perform elaboration on syntax matching `Lean.Parser.Tactic.rwRuleSeq`. -/
private def rwRuleSeqElab (rwRuleSeqStx : Syntax) : TacticM (Array Expr) :=
  let rwRuleStxsWithoutSeparators := rwRuleSeqStx[1].getArgs.getEvenElems
  rwRuleStxsWithoutSeparators.mapM λ rwRuleStx => do
    /- We expect each rule's syntax to be in a specific form; crash if not. -/
    let leftArrowStx := rwRuleStx[0]
    -- Need typed syntax for the anti-quotation below
    let rwRuleStx : Lean.TSyntax `term := Lean.TSyntax.mk rwRuleStx[1]

    -- Optional syntax (like the left arrow) is called "none" when omitted
    let hasLeftArrow := !leftArrowStx.isNone
    let rwRuleStx ←
      if hasLeftArrow then `(Rel.symm $rwRuleStx) else pure rwRuleStx
    termElab rwRuleStx

/--
Convenient top-level error handling for tactics.

If the wrapped tactic action fails, emits a human-readable message with
details of the error.
-/
private def withTacticErrorHandling (t : Tactic) : Tactic := λ stx =>
  try t stx
  catch e =>
    -- The first syntax element should be the "name" of the tactic
    dbg_trace "{stx[0]} tactic failed with: {← e.toMessageData.toString}"

/--
The "simple rewrite" tactic.

Behaves very similarly to (and was substantially copied from) Mathlib's `grw`
tactic. Many features were removed or simplified because they aren't needed for
this project's use cases.
-/
syntax (name := srwStx) "srw " rwRuleSeq : tactic

/--
Perform elaboration on the "simple rewrite" syntax.

Lean uses this to translate the tactic syntax into actual processing and state
changes in the monadic context where the tactic is used.
-/
@[tactic srwStx] def srwElab : Tactic := withTacticErrorHandling λ stx => do
  /-
  Assume these syntax elements are present, crash if not. This shouldn't be an
  issue in practice because Lean will only invoke this code when it encounters
  syntax conforming to the argument of the `@tactic` annotation.
  -/
  let rwRuleSeqStx := stx[1]

  /-
  Users expect the syntax will be able to reference entities from the main
  goal's context, thus it must be elaborated within that context.
  -/
  let goal ← getMainGoal
  goal.withContext do
    let directedRules ← rwRuleSeqElab rwRuleSeqStx
    -- The most important line; all code above is just preparing for this call
    simpleRewrite goal directedRules

/--
The "predicate rewrite" or "Prop rewrite" tactic.

Applies one or more transformations to the arguments of a relation or predicate
in `Prop`. For example, given `(α : Type) (a b c : α) (P : α → Prop)`, the
syntax `by prw [‹a ≃ b›, ‹b ≃ c›] ‹P a›` will produce a term of type `P c`.

This only works if appropriate congruence theorems have the `gcongr` attribute
attached. The example above would require a theorem like the following:

```
@[gcongr]
theorem P_subst {α : Type} {P : α → Prop} {x₁ x₂ : α} : x₁ ≃ x₂ → P x₁ → P x₂
```
-/
syntax (name := prwStx) "prw " rwRuleSeq term : tactic

/--
Perform elaboration on the "predicate rewrite" syntax.

Lean uses this to translate the tactic syntax into actual processing and state
changes in the monadic context where the tactic is used.
-/
@[tactic prwStx] def prwElab : Tactic := withTacticErrorHandling λ stx => do
  /-
  Assume these syntax elements are present, crash if not. This shouldn't be an
  issue in practice because Lean will only invoke this code when it encounters
  syntax conforming to the argument of the `@tactic` annotation.
  -/
  let rwRuleSeqStx := stx[1]
  let startTermStx := stx[2]

  /-
  Users expect the syntax will be able to reference entities from the main
  goal's context, thus it must be elaborated within that context.
  -/
  let goal ← getMainGoal
  goal.withContext do
    let directedRules ← rwRuleSeqElab rwRuleSeqStx
    let startTerm ← termElab startTermStx

    -- The most important line; all code above is just preparing for this call
    predicateRewrite goal directedRules startTerm

end Lean4Axiomatic.Tactic
