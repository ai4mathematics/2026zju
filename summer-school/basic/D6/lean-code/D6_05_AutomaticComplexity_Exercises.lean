import Std

set_option autoImplicit false

namespace D6AutomaticComplexityExercises

/- Frames: Value, Cost, and Reduction Exercises. This file stands alone. -/

inductive CostExpr where
  | const (value : Nat)
  | var (name : String)
  | add (left right : CostExpr)
  | mul (left right : CostExpr)
deriving Repr, DecidableEq

abbrev CostEnv := String -> Nat

def CostExpr.eval : CostExpr -> CostEnv -> Nat
  | .const value, _env => value
  | .var name, env => env name
  | .add left right, env => left.eval env + right.eval env
  | .mul left right, env => left.eval env * right.eval env

def CostExpr.reduceZeroLeft : CostExpr -> CostExpr
  | .add (.const 0) right => right
  | expression => expression

inductive Value where
  | nat (value : Nat)
  | bool (value : Bool)
deriving Repr, DecidableEq

inductive Term where
  | nat (value : Nat)
  | bool (value : Bool)
  | ifThenElse (condition thenBranch elseBranch : Term)
  | listInput (lengthName valueName : String)
  | mapAdd (increment : Nat) (functionCost : CostExpr) (source : Term)
deriving Repr, DecidableEq

def Term.eval : Term -> Except String Value
  | .nat value => pure (.nat value)
  | .bool value => pure (.bool value)
  | .ifThenElse condition yes no => do
      match <- condition.eval with
      | .bool true => yes.eval
      | .bool false => no.eval
      | _ => throw "if expects a Boolean"
  | .listInput _ _ => throw "value input is not needed in this exercise"
  | .mapAdd _ _ _ => throw "value map is not needed in this exercise"

def Term.lengthExpr : Term -> Option CostExpr
  | .listInput lengthName _ => some (.var lengthName)
  | .mapAdd _ _ source => source.lengthExpr
  | _ => none

def Term.cost : Term -> Except String CostExpr
  | .nat _ => pure (.const 0)
  | .bool _ => pure (.const 0)
  | .ifThenElse _ _ _ => throw "if cost is not needed in this exercise"
  | .listInput _ _ => pure (.const 0)
  | .mapAdd _ functionCost source => do
      let sourceCost <- source.cost
      match source.lengthExpr with
      | some length => pure (.add sourceCost (.mul length functionCost))
      | none => throw "map source has no known length"

theorem eval_if_true (x y : Nat) :
    (Term.ifThenElse (.bool true) (.nat x) (.nat y)).eval =
      Except.ok (.nat x) := by
  sorry

theorem map_input_cost
    (increment : Nat)
    (functionCost : CostExpr)
    (lengthName valueName : String) :
    (Term.mapAdd increment functionCost
      (.listInput lengthName valueName)).cost =
      Except.ok (.add (.const 0) (.mul (.var lengthName) functionCost)) := by
  sorry

theorem reduce_zero_left_sound
    (env : CostEnv)
    (expression : CostExpr) :
    expression.reduceZeroLeft.eval env = expression.eval env := by
  sorry

end D6AutomaticComplexityExercises
