-- D5_04: Local code for the expression-language evaluator.
-- Frames: "Abstract Syntax Trees (AST)" through "Exercise: Another Function on the Same Syntax Tree".

-- Frames: Abstract Syntax Trees (AST) / Evaluating Expressions.
inductive Expr where
  | val : Nat -> Expr
  | var : String -> Expr
  | add : Expr -> Expr -> Expr
  | mul : Expr -> Expr -> Expr
  deriving Repr

def myExpr : Expr :=
  Expr.mul (Expr.add (Expr.var "x") (Expr.val 2))
    (Expr.val 3)

#eval myExpr

abbrev Env := String -> Option Nat

def emptyEnv : Env := fun _ => none

def extendEnv (k : String) (v : Nat) (env : Env) : Env :=
  fun name => if name == k then some v else env name

-- Frame: The Evaluator (Pattern Matching & Monads).
def eval (e : Expr) (env : Env) : Option Nat :=
  match e with
  | Expr.val n => pure n
  | Expr.var s => env s
  | Expr.add l r => do
      let vl <- eval l env
      let vr <- eval r env
      pure (vl + vr)
  | Expr.mul l r => do
      let vl <- eval l env
      let vr <- eval r env
      pure (vl * vr)

def depth : Expr -> Nat
  | Expr.val _ => 1
  | Expr.var _ => 1
  | Expr.add l r => Nat.succ (Nat.max (depth l) (depth r))
  | Expr.mul l r => Nat.succ (Nat.max (depth l) (depth r))

def countVars : Expr -> Nat
  | Expr.val _ => 0
  | Expr.var _ => 1
  | Expr.add l r => countVars l + countVars r
  | Expr.mul l r => countVars l + countVars r

def collectVars : Expr -> List String
  | Expr.val _ => []
  | Expr.var s => [s]
  | Expr.add l r => collectVars l ++ collectVars r
  | Expr.mul l r => collectVars l ++ collectVars r

-- Frame: Exercise: Another Function on the Same Syntax Tree.
def myEnv : Env :=
  extendEnv "x" 5 emptyEnv

#eval eval myExpr myEnv
#eval eval (Expr.var "y") myEnv
#eval depth myExpr
#eval countVars myExpr
#eval collectVars myExpr

-- Exercises:
-- Frame: Exercise: Another Function on the Same Syntax Tree.
-- 1. Add subtraction or equality as a new constructor.
-- 2. Remove duplicate names from collectVars.
-- 3. Prove that eval (Expr.val n) env = some n.
