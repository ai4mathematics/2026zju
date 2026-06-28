/-
  D2_IntegratedExample.lean

  One coherent example connecting inductive types, pattern matching,
  recursion, Option, List, structure, deriving, and induction.
-/

namespace D2IntegratedExample

/-! ## Environments -/

structure Env where
  lookup : String -> Option Nat

def emptyEnv : Env :=
  { lookup := fun _ => none }

def sampleEnv : Env :=
  { lookup := fun name =>
      if name = "x" then
        some 10
      else if name = "y" then
        some 5
      else
        none }

#eval sampleEnv.lookup "x"
#eval sampleEnv.lookup "z"

/-! ## Expression trees -/

inductive Expr where
  | const : Nat -> Expr
  | add : Expr -> Expr -> Expr
  | var : String -> Expr
  deriving Repr, BEq, DecidableEq

namespace Expr

def eval (env : Env) : Expr -> Option Nat
  | const n => some n
  | var name => env.lookup name
  | add left right =>
      match eval env left, eval env right with
      | some m, some n => some (m + n)
      | _, _ => none

def vars : Expr -> List String
  | const _ => []
  | var name => [name]
  | add left right => vars left ++ vars right

def mirror : Expr -> Expr
  | const n => const n
  | var name => var name
  | add left right => add (mirror right) (mirror left)

def nodeCount : Expr -> Nat
  | const _ => 1
  | var _ => 1
  | add left right => nodeCount left + nodeCount right + 1

end Expr

def e1 : Expr :=
  Expr.add (Expr.var "x") (Expr.const 3)

def e2 : Expr :=
  Expr.add e1 (Expr.var "y")

def eBad : Expr :=
  Expr.add e1 (Expr.var "missing")

#eval e1
#eval Expr.eval sampleEnv e1
#eval Expr.eval sampleEnv e2
#eval Expr.eval sampleEnv eBad
#eval Expr.vars e2
#eval Expr.mirror e2
#eval Expr.nodeCount e2

/-! ## A small induction theorem -/

theorem mirror_mirror (e : Expr) :
    Expr.mirror (Expr.mirror e) = e := by
  induction e with
  | const n =>
      rfl
  | var name =>
      rfl
  | add left right ihLeft ihRight =>
      simp [Expr.mirror, ihLeft, ihRight]

/-!
Exercise ideas:
1. Add multiplication to `Expr`.
2. Extend `eval`, `vars`, `mirror`, and `nodeCount`.
3. Update the induction proof.
-/

end D2IntegratedExample
