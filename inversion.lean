module

public meta import Lean.Elab.ConfigEval
public meta import Lean.Elab.Tactic.RenameInaccessibles
public meta import Lean.Elab.Tactic.Induction
public meta import Lean.Meta.Tactic.Cases
meta import all Lean.Meta.Tactic.Cases

meta section

namespace Lean.Parser
open Tactic

/-- Internal syntactic representation of a single inversion alternative. -/
declare_syntax_cat invAlt
syntax " | " caseArg " => " tacticSeq : invAlt

/-- An inversion alternative matching one or more goal tags,
  expanding to multiple single [invAlt]s. -/
declare_syntax_cat invAlts
syntax (" | " caseArg)+ " => " tacticSeq : invAlts

/--
  `inversion t` generalizes nonvariable indices of the type of `t` before invoking `cases t`,
  then solves away contradictory generated goals.
  `t` itself will also be generalized with a heterogeneous equality `heq`
  if trying to generalize the indices produces an ill-typed result.
  * If `inversion +clear t` is set, then `heq` will be `clear`ed from the context if present,
    along with `t` if there are no dependencies on it.
  * The form `inversion t with | tag₁ x ... => tac ... | ... | tagₙ z ... => tac ...` is supported,
    similar to that of `cases` and `inversion`.
-/
syntax (name := inversion)
  "inversion " optConfig ident (" with " (colGe invAlts)+)? : tactic

end Lean.Parser

namespace Lean.Meta

/-- Given equations `eqs` in the local context of `mvarId`,
  unify them using [Lean.Meta.unifyEq?],
  but if unification fails, leave the equation in the context.
  This means we should never get a "Dependent elimination failed" error.
  While marked partial, this _should_ always terminate,
  decreasing on the sum of the sizes of the terms of each equation.

  Lifted from [Lean.Meta.Cases.unifyEqs]. -/
partial def unifyEqs (eqs : List FVarId) (mvarId : MVarId) (subst : FVarSubst) (caseName? : Option Name) : MetaM (MVarId × FVarSubst) := withIncRecDepth do
  match eqs with
  | [] => return (mvarId, subst)
  | eq :: eqs =>
    let some { mvarId, subst, numNewEqs } ← Option.join <$> (observing? $ unifyEq? mvarId eq subst MVarId.acyclic caseName?)
      | unifyEqs eqs mvarId subst caseName?
    let (newEqs, mvarId) ← mvarId.introN numNewEqs
    let eqs := eqs.map (Expr.fvarId! ∘ subst.get)
    unifyEqs (newEqs.toList ++ eqs) mvarId subst caseName?

/-- Lifted from [Lean.Meta.Cases.unifyCasesEqs]. -/
def unifyCasesEqs (eqs : List FVarId) (subgoals : Array CasesSubgoal) : MetaM (Array CasesSubgoal) :=
  subgoals.filterMapM fun s => do
    let eqs := eqs.filterMap (Expr.fvarId? ∘ s.subst.get)
    let (mvarId, subst) ← unifyEqs eqs s.mvarId s.subst s.ctorName
    if (← mvarId.isAssignedOrDelayedAssigned) then return none
    else return some { s with
      mvarId := mvarId,
      subst  := subst,
      fields := s.fields.map (subst.apply ·)
    }

/-- Try to clear the given fvars from the local context of each subgoal,
  using the subgoals' substitution mappings to find the fvars.

  As with [MVarId.tryClearMany], the fvars must be in the order they appear in the context.  -/
def casesClearMany (subgoals : Array CasesSubgoal) (fvarIds : Array FVarId) : MetaM (Array CasesSubgoal) :=
  subgoals.mapM fun s => do
    let fvarIds := fvarIds.filterMap (Expr.fvarId? ∘ s.subst.get)
    let mvarId ← s.mvarId.tryClearMany fvarIds
    return { s with mvarId }

end Lean.Meta

namespace Lean.Elab.Tactic
open Meta Term

structure InversionConfig where
  clear : Bool := false

declare_config_elab elabInversionConfig InversionConfig

open Cases in
def inversionCore (h : FVarId) (config : InversionConfig) : TacticM (List CasesSubgoal) := withMainContext do
  let goal ← getMainGoal
  goal.withContext do
    let some ctx ← mkCasesContext? h
    | throwTacticEx `inversion goal "Target {Expr.fvar h} does not belong to an inductive type"
    -- If the target's type isn't a predicate with indices, behave like `cases`
    if ← hasIndepIndices ctx then
      let subgoals ← inductionCasesOn goal h default ctx
      let subgoals ← if config.clear
        then casesClearMany subgoals #[h]
        else pure subgoals
      return subgoals.toList
    -- Otherwise, use custom [unifyEqs] to not fail on unifying HEqs
    else
      let gis@⟨newGoal, _, newTarget, numEqs⟩ ← generalizeIndices goal h
      let (newEqs, newGoal) ← newGoal.introN numEqs
      let some targetEq := newEqs.back?
      | throwTacticEx `inversion newGoal "Failed to generalize target"
      let subgoals ← inductionCasesOn newGoal newTarget default ctx
      let subgoals ← elimAuxIndices gis subgoals
      let subgoals ← unifyCasesEqs newEqs.toList subgoals
      let subgoals ← if config.clear
        then casesClearMany subgoals #[h, targetEq]
        else pure subgoals
      return subgoals.toList

open Parser Tactic in
/-- Given an inversion alternative and a list of goals,
  solve the tagged goal with the provided tactics,
  throwing an error if the goal cannot be found or solved. -/
def evalInvAlt (goals : List CasesSubgoal) (alt : TSyntax `invAlt) : TacticM (List MVarId) :=
  match alt with
  | `(invAlt| | $tag:ident $vars:binderIdent* => $tactics:tacticSeq) => do
    if let some goal := goals.find? (matchTag tag.getId $ ·.ctorName.getD default) then
      return [← trySolveGoal vars tactics goal.mvarId]
    else throwError m!"Invalid alternative name `{tag.getId}`: {← errorMsg}"
  | `(invAlt| | _ $vars:binderIdent* => $tactics:tacticSeq) => do
    if !goals.isEmpty then
      goals.mapM (trySolveGoal vars tactics ·.mvarId)
    else throwErrorAt alt m!"Invalid wildcard alternative: {← errorMsg}"
  | _ => throwErrorAt alt "Could not parse inversion alternative"
where
  matchTag (tag name : Name) : Bool :=
    tag == name || tag.isPrefixOf name || tag.isSuffixOf name
  trySolveGoal (vars : TSyntaxArray ``binderIdent) (tactics : TSyntax ``tacticSeq) (goal : MVarId) : TacticM MVarId := do
    let goals ← renameInaccessibles goal vars >>= evalTacticAt tactics
    unless goals.isEmpty do
      reportUnsolvedGoals goals
    return goal
  errorMsg : TacticM MessageData := do
    let goalMsgs := goals.filterMap (.ofName <$> ·.ctorName)
    return if goals.isEmpty
      then m!"There are no unhandled alternatives"
      else m!"Expected {.orList goalMsgs}"

@[tactic Lean.Parser.inversion, inherit_doc Lean.Parser.inversion]
public meta def evalInversion : Tactic
  | `(tactic| inversion $config $h:ident $[with $[$alts?:invAlts]*]?) => do
    let config ← elabInversionConfig config
    let mut goals ← inversionCore (← getFVarId h) config
    if let some alts := alts? then
      let expandedAlts ← Array.flatten <$> alts.mapM expandInvAlts
      for alt in expandedAlts do
        let solvedGoals ← evalInvAlt goals alt
        goals := goals.filter (!solvedGoals.contains ·.mvarId)
      unless goals.isEmpty do
        reportUnsolvedGoals $ goals.map (·.mvarId)
    replaceMainGoal $ goals.map (·.mvarId)
  | stx => throwErrorAt stx "Could not parse inversion tactic"
where expandInvAlts
  | `(invAlts| $[| $args:caseArg]* => $tactics:tacticSeq) =>
    args.mapM (`(invAlt| | $(·) => $tactics))
  | stx => throwErrorAt stx "Could not parse inversion alternatives"

end Lean.Elab.Tactic

end -- meta section

namespace Tests
open Nat

set_option autoImplicit false
set_option pp.proofs true
set_option pp.fieldNotation false

/-- error: Dependent elimination failed: Failed to solve equation
  0 = f n -/
#guard_msgs(error) in
example (f : Nat → Nat) (n : Nat) (leq : f n ≤ 0) : 0 = f n := by
  cases leq

example (f : Nat → Nat) (n : Nat) (leq : f n ≤ 0) : 0 = f n := by
  -- cases leq /- Dependent elimination failed: Failed to solve equation 0 = f n -/
  inversion leq; assumption

example (f : Nat → Nat) (n : Nat) (leq : f n ≤ 0) : 0 = f n := by
  inversion +clear leq; assumption

/-- error: Unknown identifier `leq` -/
#guard_msgs(error) in
example (f : Nat → Nat) (n : Nat) (leq : f n ≤ 0) : 0 = f n := by
  inversion +clear leq
  guard_hyp leq

example (f : Nat → Nat) (n : Nat) (leq : f n ≤ 0) : 0 = f n := by
  inversion leq with
  | refl heq eq =>
    guard_hyp heq : leq ≍ le.refl
    guard_hyp eq : 0 = f n
    assumption

/-- warning: declaration uses `sorry` -/
#guard_msgs(warning) in
example (f : Nat → Nat) (n m : Nat) (leq : f n ≤ f m) : f n = 0 := by
  inversion leq with
  | refl e _ | step k _ e _ =>
    try rw [← eq]
    sorry

/-- error: Invalid wildcard alternative: There are no unhandled alternatives -/
#guard_msgs(error) in
example (f : Nat → Nat) (n m : Nat) (leq : f n ≤ f m) : f n = 0 := by
  inversion +clear leq with
  | refl e | step k _ e =>
    try rw [← e]
    sorry
  | _ => sorry

/-- error: Invalid alternative name `step`: There are no unhandled alternatives -/
#guard_msgs(error) in
example (f : Nat → Nat) (n m : Nat) (leq : f n ≤ f m) : f n = 0 := by
  inversion +clear leq with
  | _ e | step k _ e =>
    try rw [← e]
    sorry

inductive The : ∀ {α}, α → Prop where
  | mk : The zero

/-- Case names should be the constructors' names -/
example {x : Nat} (h : The x) : x = zero := by
  inversion h with
  | mk => rfl

example (n m o : Nat) : [n, m] = [o, o] → [n] = [m] := by
  intro h
  inversion h; rfl

inductive NoStutter {α : Type} : List α → Prop where
  | nostutter0: NoStutter []
  | nostutter1 n : NoStutter (n::[])
  | nostutter2 a b r (hneq : a ≠ b) (h : NoStutter (b::r)) : NoStutter (a::b::r)

/-- The last (only) case name need not be provided -/
example : ¬ (NoStutter [3, 1, 1, 4]) := by
  intro contra
  inversion contra with | _ contra =>
  inversion contra with | _ h _ =>
  apply h
  rfl

inductive Vec α : Nat → Type where
  | nil : Vec α 0
  | cons {n} : α → Vec α n → Vec α (n + 1)

/-- Inversion should work on indexed `Type`s as well -/
example {α} (n : Nat) (v : Vec α (n + 1)) : ∃ hd tl, v = Vec.cons hd tl := by
  inversion v with
  | cons hd tl => exists hd, tl

inductive Wec α : Nat → Type where
  | nil : Wec α 0
  | cons {n} (f : Nat → Nat) : α → Wec α n → Wec α (f n)

/-- warning: declaration uses `sorry` -/
#guard_msgs(warning) in
example {α} (n : Nat) (v : Wec α (succ n)) :
    ∃ hd tl, v = Wec.cons succ hd tl := by
  inversion v with
  | cons m f hd tl eq heq =>
    guard_hyp eq : succ n = f m
    guard_hyp heq : v ≍ Wec.cons f hd tl
    sorry

inductive EmptyRelation : Nat → Nat → Prop where

/-- Inversion should still work on nonindexed `Prop`s -/
example n m : ¬ EmptyRelation n m := by
  intro contra; inversion contra

/-- With `inductive.autoPromoteIndices` true (the default),
  this is also a nonindexed `Prop`... -/
inductive silly : Nat → Prop where
| silly1 n (h : n > 1) : silly n
| silly2 n (h : exists m, m * 2 = n) : silly n
| silly3 n (h : exists m, n = m + 2) : silly n

/-- ...and inversion should continue to work -/
example {n} (h : silly n) : n ≠ 1 := by
  inversion h <;> omega

/-- Inversion should also work on nonindexed `Type`s -/
example (n : Nat) : Nat := by
  inversion n with
  | zero => exact zero
  | succ n' => exact n'

end Tests
