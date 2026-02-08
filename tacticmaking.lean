import Lean
open Lean Meta Elab Tactic


namespace TacticMaking

syntax (name := my_assumption_syntax) "my_assumption" : tactic

@[tactic my_assumption_syntax]
def my_asssumption_elab : Tactic := fun stx => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  -- logInfo s!"{goalType}"
  goal.withContext do
    let lctx ← getLCtx
    for decl in lctx do
      -- logInfo s!"{decl.type}"
      if ← isDefEq decl.type goalType then
        goal.assign decl.toExpr
        return
    throwError s!"my_assumption failed to find a matching local declaration with type {goalType}."
  return

example (x y : Nat) (h : x = y) : x = y := by
  my_assumption

example (x y z : Nat) (h : x = z) : x = y := by
  my_assumption

example : forall (x y : Nat), x = y → x = y := by
  my_assumption
end TacticMaking
