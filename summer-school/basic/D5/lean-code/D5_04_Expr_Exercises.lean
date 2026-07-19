-- D5_04 exercises: easy functions on the same Expr syntax tree.
-- The evaluator is provided as context; the exercise functions are below it.

-- Frames: Abstract Syntax Trees (AST) / The Evaluator.
inductive Expr where
  | val : Nat -> Expr
  | var : String -> Expr
  | add : Expr -> Expr -> Expr
  | mul : Expr -> Expr -> Expr
  deriving Repr

def myExpr : Expr :=
  Expr.mul (Expr.add (Expr.var "x") (Expr.val 2))
    (Expr.val 3)

abbrev Env := String -> Option Nat

def emptyEnv : Env := fun _ => none

def extendEnv (k : String) (v : Nat) (env : Env) : Env :=
  fun name => if name == k then some v else env name

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

-- Frame: Exercise: Another Function on the Same Syntax Tree.
def exDepth : Expr -> Nat
  | Expr.val _ => by
      sorry
  | Expr.var _ => by
      sorry
  | Expr.add l r => by
      sorry
  | Expr.mul l r => by
      sorry

def exCountVars : Expr -> Nat
  | Expr.val _ => by
      sorry
  | Expr.var _ => by
      sorry
  | Expr.add l r => by
      sorry
  | Expr.mul l r => by
      sorry

def exCollectVars : Expr -> List String
  | Expr.val _ => by
      sorry
  | Expr.var s => by
      sorry
  | Expr.add l r => by
      sorry
  | Expr.mul l r => by
      sorry

