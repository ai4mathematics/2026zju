import Lean

-- D5_06: Local code for the meta-programming block.
-- Frames: "Writing a Macro", "Writing a Command Elaborator",
-- "Writing a Tactic Elaborator", and "Reusing Existing Tactics".

open Lean Elab Command Elab.Tactic

-- Frame: Writing a Macro.
syntax:10 term:10 " XOR " term:11 : term

macro_rules
  | `($l XOR $r) => `((!$l && $r) || ($l && !$r))

#eval true XOR false
#eval true XOR true

-- Frame: Writing a Command Elaborator.
elab "#hello" : command => do
  logInfo "Hello from the elaborator!"

#hello

-- Frame: Writing a Tactic Elaborator: Interacting with State.
elab "print_goal" : tactic => do
  let mvarId <- getMainGoal
  let decl <- mvarId.getDecl
  logInfo m!"The current goal type is: {decl.type}"

example : True := by
  print_goal
  trivial

-- Frame: Reusing Existing Tactics: evalTactic.
elab "custom_intro " name:ident : tactic => do
  evalTactic (← `(tactic| intro $name:ident))

example : True -> True := by
  custom_intro h
  exact h
