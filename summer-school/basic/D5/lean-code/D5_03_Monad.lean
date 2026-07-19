-- D5_03: Local code for the monad block.
-- Frames: "Monad intro 5" through "Monad Transformers: stacking effects".

-- Frames: Option, do-notation, and the first Option exercise.
def safeDiv (a b : Nat) : Option Nat :=
  if b == 0 then none else some (a / b)

def divTwice (a b c : Nat) : Option Nat := do
  let x <- safeDiv a b
  let y <- safeDiv x c
  pure y

def addOpt_bind (x y : Option Nat) : Option Nat :=
  x >>= fun a => y >>= fun b => pure (a + b)

def addOpt_app (x y : Option Nat) : Option Nat :=
  pure Nat.add <*> x <*> y

def addOpt_do (x y : Option Nat) : Option Nat := do
  let a <- x
  let b <- y
  pure (a + b)

def safePred : Nat -> Option Nat
  | 0 => none
  | n + 1 => some n

def predThenHalf (n : Nat) : Option Nat := do
  let m <- safePred n
  safeDiv m 2

#eval divTwice 100 5 4
#eval addOpt_app (some 3) (some 4)
#eval addOpt_do (some 3) none
#eval predThenHalf 9
#eval predThenHalf 0

-- Frame: Except: failure with a message.
def safeIndexE : Nat -> List Nat -> Except String Nat
  | _, [] => .error "index out of bounds"
  | 0, x :: _ => .ok x
  | n + 1, _ :: xs => safeIndexE n xs

def safeHeadE : List Nat -> Except String Nat
  | [] => .error "empty list"
  | x :: _ => .ok x

def addThirdAndFourth (xs : List Nat) : Except String Nat := do
  let a <- safeIndexE 2 xs
  let b <- safeIndexE 3 xs
  pure (a + b)

#eval addThirdAndFourth [10, 20, 30, 40, 50]
#eval safeHeadE []

-- Frame: The Reader Monad (ReaderM).
structure AppConfig where
  dbHost : String
  port : Nat

def buildConnectionUrl : ReaderM AppConfig String := do
  let cfg <- read
  pure s!"http://{cfg.dbHost}:{cfg.port}/api"

#eval buildConnectionUrl { dbHost := "localhost", port := 8080 }

-- Frames: The State Monad and its exercise.
def tick : StateM Nat Nat := do
  modify (fun n => n + 1)
  get

def incrementAndGet : StateM Nat Nat := tick

def tickTwice : StateM Nat Nat := do
  discard tick
  tick

def sumThreeTicks : Nat × Nat :=
  (do
    let a <- tick
    let b <- tick
    let c <- tick
    pure (a + b + c)).run 0

#eval tickTwice.run 0
#eval sumThreeTicks

-- Frames: Writer-style logging with standard StateM.
def logOneMessage : StateM (Array String) Unit := do
  modify (fun logs => logs.push "started")

def divideWithLog (a b : Nat) : StateM (Array String) Nat := do
  if b == 0 then
    modify (fun logs => logs.push "Error: division by zero attempted")
    pure 0
  else
    modify (fun logs => logs.push s!"Dividing {a} by {b}")
    pure (a / b)

#eval logOneMessage.run #[]
#eval (divideWithLog 8 2).run #[]

def counterDemo : IO Unit := do
  let r <- IO.mkRef 0
  r.modify (fun n => n + 1)
  r.modify (fun n => n + 1)
  let n <- r.get
  IO.println s!"counter = {n}"

def greet : IO Unit := do
  IO.println "Functional programming keeps effects explicit."

-- Frame: Monad Transformers: stacking effects.
abbrev SymbolTable := List String
abbrev CompilerM := StateT SymbolTable (Except String)

-- Exercises for class:
-- Frame: Break 2: Tree, Graph, and Monad Checkpoint.
-- 1. Re-derive predThenHalf from safePred and safeDiv.
-- 2. Write a variant of safeIndexE that returns the first two elements as a pair.
-- 3. Extend the StateM logging example with one more message of your own.
