module

public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Meta.Tactic.Generalize
public meta import Lean.Meta.Tactic.Cases
public meta import Lean.Meta.Tactic.Contradiction

namespace Lean.Elab.Tactic
open Meta

elab "inversion " targetName:term : tactic => withMainContext do
  let mvarId ← getMainGoal
  let target ← elabTerm targetName none
  let targetId := target.fvarId!
  let targetName ← targetId.getUserName
  let targetType ← inferType target
  let targetType ← whnf targetType
  let ⟨indName, args⟩ := targetType.getAppFnArgs
  match ← isInductive? indName with
  | some indVal =>
    let indices := args.drop indVal.numParams
    let nonvars := indices.filter (not ·.isFVar)
    let genargs : Array GeneralizeArg :=
      nonvars.map ({ expr := ·, hName? := some (← mkFreshUserName $ targetName.append `eq) })
    let ⟨substs, _, mvarId⟩ ← mvarId.generalizeHyp genargs #[targetId]
    let .some newTarget := substs.map.find? targetId
      | throwTacticEx `inversion mvarId m!"failed to generalize argument"
    mvarId.withContext do
      let subgoals ← mvarId.cases newTarget.fvarId!
      let subgoals := subgoals.map (·.mvarId)
      let subgoals ← subgoals.filterM (not <$> ·.contradictionCore {})
      replaceMainGoal $ subgoals.toList
  | none =>
    throwTacticEx `inversion mvarId
      m!"target is not an inductive type{indentExpr targetType}"

end Tactic

example (f : Nat → Nat) (n : Nat) (le : f n ≤ 0) : f n = 0 := by
  -- cases le /- Dependent elimination failed: Failed to solve equation 0 = f n -/
  inversion le; rfl
