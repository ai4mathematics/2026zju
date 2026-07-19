import Std

set_option autoImplicit false

namespace D6MonadSupplementExercises

/- Frames: Small Exercises after Reader, Writer, State, and ExceptT.
   This file is complete by itself. Fill the five easy holes, then run main. -/

structure AppConfig where
  course : String
  bonus : Nat
deriving Repr

structure Writer (Alpha : Type) where
  value : Alpha
  log : List String
deriving Repr

instance : Monad Writer where
  pure value := { value, log := [] }
  bind action next :=
    let result := next action.value
    { value := result.value, log := action.log ++ result.log }

def tell (message : String) : Writer PUnit :=
  { value := PUnit.unit, log := [message] }

def Writer.run {Alpha : Type} (action : Writer Alpha) : Alpha × List String :=
  (action.value, action.log)

end D6MonadSupplementExercises

open D6MonadSupplementExercises

def main : IO Unit := do
  let config : AppConfig := { course := "Lean", bonus := 3 }
  let readerProgram : ReaderM AppConfig Nat := do
    let current <- read
    pure (sorry)
  IO.println s!"Reader bonus: {readerProgram.run config}"

  let input : Nat := 4
  let writerProgram : Writer Nat := do
    tell "start"
    let doubled := input * 2
    tell (sorry)
    pure doubled
  IO.println s!"Writer: {reprStr writerProgram.run}"

  let initialCounter : Nat := 10
  let stateProgram : StateM Nat Nat := do
    modify (fun counter => sorry)
    get
  IO.println s!"State: {reprStr (stateProgram.run initialCounter)}"

  let initialBalance : Nat := 10
  let withdraw : Nat -> ExceptT String (StateM Nat) Nat := fun amount => do
    let balance <- get
    if amount <= balance then
      modify (fun current => sorry)
      get
    else
      throw (sorry)
  IO.println s!"Success: {reprStr ((withdraw 4).run.run initialBalance)}"
  IO.println s!"Failure: {reprStr ((withdraw 20).run.run initialBalance)}"
