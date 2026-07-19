-- D5_03 exercises: easy monad programs.
-- The file keeps only small Option, Except, ReaderM, and StateM tasks.

-- Frames: Option / Exercise: Another Small Option Program.
def safeDiv (a b : Nat) : Option Nat :=
  if b == 0 then none else some (a / b)

def exAddOptDo (x y : Option Nat) : Option Nat := by
  sorry

def exSafePred : Nat -> Option Nat
  | 0 => by
      sorry
  | n + 1 => by
      sorry

def exPredThenHalf (n : Nat) : Option Nat := do
  let m <- exSafePred n
  -- Reuse safeDiv here.
  sorry

-- Frame: Except: failure with a message.
def exSafeHeadE : List Nat -> Except String Nat
  | [] => by
      sorry
  | x :: _ => by
      sorry

-- Frame: Exercise: ReaderM and an Environment.
structure AppConfig where
  dbHost : String
  port : Nat

def exBuildConnectionUrl : ReaderM AppConfig String := do
  let cfg <- read
  sorry

-- Frame: Exercise: Writer-style logging with standard StateM.
def exDivideWithLog (a b : Nat) : StateM (Array String) Nat := do
  modify (fun logs => logs.push s!"Dividing {a} by {b}")
  sorry

-- Frame: Exercise: One State Step More.
def tick : StateM Nat Nat := do
  modify (fun n => n + 1)
  get

def exTickTwice : StateM Nat Nat := by
  sorry
