import Std

set_option autoImplicit false

namespace D6MonadSupplement

/- Frames: The Type Shapes Behind the APIs.
   ReaderM, StateM, and ExceptT come from Lean. Lean core has no separate
   WriterT, so this file defines the smallest Writer needed for tell/listen. -/

#print ReaderT
#print ReaderM
#print StateT
#print StateM
#print ExceptT
#print ReaderT.run
#print read
#print withReader
#print StateT.run
#print get
#print set
#print modify
#print ExceptT.run
#print throw
#print tryCatch

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

def listen {Alpha : Type} (action : Writer Alpha) : Writer (Alpha × List String) :=
  { value := (action.value, action.log), log := action.log }

def Writer.run {Alpha : Type} (action : Writer Alpha) : Alpha × List String :=
  (action.value, action.log)

end D6MonadSupplement

open D6MonadSupplement

/- Frames: One Main Supplies the Starting Values Once.
   Each monadic program is a local value. Read every do block from top to
   bottom; understanding the implementation of bind can come later. -/

def main : IO Unit := do
  let config : AppConfig := { course := "Lean", bonus := 3 }
  let readerProgram : ReaderM AppConfig String := do
    let original <- read
    let localCourse <- withReader
      (fun cfg => { cfg with course := cfg.course ++ " workshop" }) do
        let changed <- read
        pure changed.course
    let restored <- read
    pure s!"{original.course}; {localCourse}; {restored.course}"
  let readerResult := readerProgram.run config
  IO.println s!"Reader: {readerResult}"

  let input : Nat := 4
  let writerProgram : Writer Nat := do
    tell s!"input = {input}"
    let doubled := input * 2
    let observed <- listen (do
      tell s!"doubled = {doubled}"
      pure doubled)
    tell s!"listen saw {observed.2.length} message"
    pure observed.1
  let writerResult := writerProgram.run
  IO.println s!"Writer: {reprStr writerResult}"

  let initialCounter : Nat := 10
  let stateProgram : StateM Nat (Nat × Nat) := do
    let before <- get
    modify (fun counter => counter + 5)
    let after <- get
    pure (before, after)
  let stateResult := stateProgram.run initialCounter
  IO.println s!"State: {reprStr stateResult}"

  let initialBalance : Nat := 10
  let withdraw : Nat -> ExceptT String (StateM Nat) Nat := fun amount => do
    let balance <- get
    if amount <= balance then
      modify (fun current => current - amount)
      get
    else
      throw s!"need {amount}, but have {balance}"
  let successfulResult := (withdraw 4).run.run initialBalance
  let failedResult := (withdraw 20).run.run initialBalance
  IO.println s!"ExceptT success: {reprStr successfulResult}"
  IO.println s!"ExceptT failure: {reprStr failedResult}"

  let recovered : ExceptT String (StateM Nat) Nat :=
    tryCatch (withdraw 20) fun _message => get
  let recoveredResult := recovered.run.run initialBalance
  IO.println s!"ExceptT recovered: {reprStr recoveredResult}"
