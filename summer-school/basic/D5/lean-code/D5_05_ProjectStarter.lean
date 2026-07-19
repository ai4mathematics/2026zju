-- D5_05: Starter file for the mini-language project.
-- Frames: "Project: Build a Mini Language in Lean 4" through "Exercise: A Small Local Extension of the Project".

-- Frames: Project Requirements / Following the 48-Hour Scheme Framework.
inductive RichExpr where
  | natLit : Nat -> RichExpr
  | boolLit : Bool -> RichExpr
  | var : String -> RichExpr
  | add : RichExpr -> RichExpr -> RichExpr
  | less : RichExpr -> RichExpr -> RichExpr
  | ite : RichExpr -> RichExpr -> RichExpr -> RichExpr
  | letE : String -> RichExpr -> RichExpr -> RichExpr
  deriving Repr

inductive Val where
  | natV : Nat -> Val
  | boolV : Bool -> Val
  deriving Repr, BEq

abbrev Env := String -> Option Val

def emptyEnv : Env := fun _ => none

def extend (k : String) (v : Val) (env : Env) : Env :=
  fun name => if name == k then some v else env name

def lookup (x : String) (env : Env) : Except String Val :=
  match env x with
  | some v => pure v
  | none => .error s!"unbound variable: {x}"

def asNat : Val -> Except String Nat
  | .natV n => pure n
  | .boolV _ => .error "expected a natural number"

def asBool : Val -> Except String Bool
  | .boolV b => pure b
  | .natV _ => .error "expected a boolean"

-- Frame: Project Requirements.
def eval (e : RichExpr) (env : Env) : Except String Val :=
  match e with
  | .natLit n => pure (.natV n)
  | .boolLit b => pure (.boolV b)
  | .var x => lookup x env
  | .add e1 e2 => do
      let n1 <- asNat (← eval e1 env)
      let n2 <- asNat (← eval e2 env)
      pure (.natV (n1 + n2))
  | .less e1 e2 => do
      let n1 <- asNat (← eval e1 env)
      let n2 <- asNat (← eval e2 env)
      pure (.boolV (n1 < n2))
  | .ite c t e => do
      let b <- asBool (← eval c env)
      if b then
        eval t env
      else
        eval e env
  | .letE x rhs body => do
      let v <- eval rhs env
      eval body (extend x v env)

def sampleProgram : RichExpr :=
  .letE "x" (.natLit 7)
    (.ite (.less (.var "x") (.natLit 10))
      (.add (.var "x") (.natLit 1))
      (.natLit 0))

#eval eval sampleProgram emptyEnv

-- Suggested extensions:
-- Frame: Exercise: A Small Local Extension of the Project.
-- 1. Add multiplication, equality, or unary negation.
-- 2. Replace String variables with a custom Name type.
-- 3. Add lambdas and closures if the core evaluator is stable.
