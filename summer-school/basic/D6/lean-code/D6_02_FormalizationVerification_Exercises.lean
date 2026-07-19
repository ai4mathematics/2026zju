import Std

set_option autoImplicit false

namespace D6FormalizationVerificationExercises

/- Frames: SExpr Syntax, Evaluation, and First-Break Practice.
   This file is standalone: it does not import another lecture file. -/

inductive SExpr where
  | int (value : Int)
  | bool (value : Bool)
  | symbol (name : String)
  | add (left right : SExpr)
  | ifThenElse (condition thenBranch elseBranch : SExpr)

inductive SVal where
  | int (value : Int)
  | bool (value : Bool)
deriving DecidableEq, Repr

abbrev Env := String -> Option SVal

def emptyEnv : Env := fun _name => none

def eval (env : Env) : SExpr -> Except String SVal
  | .int value => pure (.int value)
  | .bool value => pure (.bool value)
  | .symbol name =>
      match env name with
      | some value => pure value
      | none => throw s!"unbound symbol: {name}"
  | .add left right => do
      match <- eval env left, <- eval env right with
      | .int x, .int y => pure (.int (x + y))
      | _, _ => throw "add expects two integers"
  | .ifThenElse condition yes no => do
      match <- eval env condition with
      | .bool true => eval env yes
      | .bool false => eval env no
      | _ => throw "if expects a Boolean"

/- First predict each result by tracing eval. Then replace only `sorry`. -/

theorem eval_if_false (x y : Int) :
    eval emptyEnv (.ifThenElse (.bool false) (.int x) (.int y)) =
      .ok (.int y) := by
  sorry

theorem eval_add_literals :
    eval emptyEnv (.add (.int 2) (.int 3)) = .ok (.int 5) := by
  sorry

theorem eval_unbound_symbol :
    eval emptyEnv (.symbol "missing") =
      .error "unbound symbol: missing" := by
  sorry

/- Reference frames: A Tiny Compiler and Its Correctness Theorem.
   The source evaluator and target machine are separate definitions. -/

inductive SrcExpr where
  | lit (value : Nat)
  | add (left right : SrcExpr)

inductive Instr where
  | push (value : Nat)
  | add

def evalSrc : SrcExpr -> Nat
  | .lit value => value
  | .add left right => evalSrc left + evalSrc right

def exec : List Instr -> List Nat -> Option (List Nat)
  | [], stack => some stack
  | .push value :: code, stack => exec code (value :: stack)
  | .add :: code, right :: left :: stack => exec code ((left + right) :: stack)
  | .add :: _code, _stack => none

def compile : SrcExpr -> List Instr
  | .lit value => [.push value]
  | .add left right => compile left ++ compile right ++ [.add]

theorem exec_append (first second : List Instr) (stack : List Nat) :
    exec (first ++ second) stack =
      (exec first stack).bind (exec second) := by
  induction first generalizing stack with
  | nil => rfl
  | cons instruction first ih =>
      cases instruction with
      | push value => exact ih (value :: stack)
      | add =>
          cases stack with
          | nil => rfl
          | cons right rest =>
              cases rest with
              | nil => rfl
              | cons left stack => exact ih ((left + right) :: stack)

theorem compile_correct (expression : SrcExpr) (stack : List Nat) :
    exec (compile expression) stack = some (evalSrc expression :: stack) := by
  induction expression generalizing stack with
  | lit value => rfl
  | add left right leftIH rightIH =>
      simp [compile, exec_append, leftIH, rightIH, exec, evalSrc]

/- These compiler checks are optional and intentionally concrete. -/

theorem compile_literal (value : Nat) (stack : List Nat) :
    exec (compile (.lit value)) stack = some (value :: stack) := by
  sorry

theorem compile_two_plus_three :
    exec (compile (.add (.lit 2) (.lit 3))) [] = some [5] := by
  sorry

end D6FormalizationVerificationExercises
