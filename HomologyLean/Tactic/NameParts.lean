import Mathlib.Tactic

open Lean Meta Elab Tactic

namespace HomologyLean.Tactic.NameParts

/--
`name_parts` pattern-matches the goal's structure and introduces `let` bindings for each named
hole (`?A`, `?B`, ...) in the pattern.

Uses `change`-style elaboration (elaborating against the goal type) to avoid the stuck-typeclass
problems that `refine`/`set` hit on complex goals. After unification, each named metavariable's
assignment becomes a `let` definition in the context.

Example:
```
-- Goal: (ρ_ X).inv ≫ f ≫ g = (ρ_ X).inv ≫ h + k
name_parts ?A = ?B + ?C
-- Context gains:  A := (ρ_ X).inv ≫ f ≫ g,  B := (ρ_ X).inv ≫ h,  C := k
-- Goal becomes:   A = B + C
```
-/
elab "name_parts " pat:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let targetType ← inferType target
  let mvarCounterBefore := (← getMCtx).mvarCounter
  -- Elaborate the pattern with inPattern=true so that ?name holes become natural mvars
  -- (not syntheticOpaque). Natural mvars can be assigned by isDefEq, avoiding stuck
  -- typeclass issues that occur when two named holes appear under the same operator.
  let pat' ← runTermElab do
    let p ← withTheReader Term.Context (fun ctx => { ctx with inPattern := true }) do
      Term.elabTermEnsuringType pat targetType
    unless ← isDefEq p target do
      Term.synthesizeSyntheticMVars (postpone := .partial)
      unless ← isDefEq p target do
        throwError "name_parts: pattern does not unify with the goal"
    instantiateMVars p
  -- Collect named metavariables that were created during elaboration and assigned by unification.
  -- Named holes (`?A`) get a non-anonymous userName; anonymous holes (`_`) are skipped.
  let mctx ← getMCtx
  let mut bindings : Array (Name × Expr × Expr × Nat) := #[]
  for (mvarId, decl) in mctx.decls do
    if decl.userName.isAnonymous then continue
    let numIdx := match mvarId.name with
      | .num _ n => n
      | _ => 0
    if numIdx < mvarCounterBefore then continue
    if let some val ← getExprMVarAssignment? mvarId then
      let val ← instantiateMVars val
      let ty ← inferType val
      bindings := bindings.push (decl.userName, ty, val, numIdx)
  -- Sort by mvar index so bindings appear in pattern order (left-to-right)
  let sortedBindings := bindings.qsort (fun a b => a.2.2.2 < b.2.2.2)
  if sortedBindings.isEmpty then
    throwError "name_parts: no named holes (?A, ?B, ...) found in the pattern"
  -- Replace the goal with the unified pattern, then layer on let-bindings.
  liftMetaTactic1 fun g => do
    let g ← g.replaceTargetDefEq pat'
    let mut g := g
    for (name, ty, val, _) in sortedBindings.reverse do
      let g' ← g.define name ty val
      let (_, g'') ← g'.intro1P
      g := g''
    pure g

end HomologyLean.Tactic.NameParts
