import Std

set_option autoImplicit false

namespace D6AutomaticComplexity

/- Frames: The Symbolic Cost Language. -/
inductive CostExpr where
  | const (value : Nat)
  | var (name : String)
  | add (left right : CostExpr)
  | mul (left right : CostExpr)
  | max (left right : CostExpr)
deriving Repr, DecidableEq

abbrev CostEnv := String -> Nat

def CostExpr.eval : CostExpr -> CostEnv -> Nat
  | .const value, _ => value
  | .var name, env => env name
  | .add left right, env => left.eval env + right.eval env
  | .mul left right, env => left.eval env * right.eval env
  | .max left right, env => Nat.max (left.eval env) (right.eval env)

/- Frames: One Reduction Rule and Its Soundness Proof. -/
def CostExpr.reduceZeroLeft : CostExpr -> CostExpr
  | .add (.const 0) right => right
  | expression => expression

theorem CostExpr.reduceZeroLeft_sound
    (env : CostEnv)
    (expression : CostExpr) :
    (expression.reduceZeroLeft).eval env = expression.eval env := by
  cases expression with
  | add left right =>
      cases left with
      | const value =>
          cases value <;> simp [CostExpr.reduceZeroLeft, CostExpr.eval]
      | var name => rfl
      | add first second => rfl
      | mul first second => rfl
      | max first second => rfl
  | _ => rfl

def CostExpr.foldConstantAdd : CostExpr -> CostExpr
  | .add (.const left) (.const right) => .const (left + right)
  | expression => expression

theorem CostExpr.foldConstantAdd_sound
    (env : CostEnv)
    (expression : CostExpr) :
    (expression.foldConstantAdd).eval env = expression.eval env := by
  cases expression with
  | add left right =>
      cases left <;> cases right <;> rfl
  | _ => rfl

/- Frames: A Small FP Term Language.
   mapAdd keeps the value semantics executable while fnCost documents the
   symbolic cost assigned to one function application. -/
inductive Value where
  | nat (value : Nat)
  | bool (value : Bool)
  | list (values : List Nat)
deriving Repr, DecidableEq

inductive Term where
  | nat (value : Nat)
  | bool (value : Bool)
  | variable (name : String)
  | add (left right : Term)
  | ifThenElse (condition thenBranch elseBranch : Term)
  | list (values : List Nat)
  | listInput (lengthName valueName : String)
  | mapAdd (increment : Nat) (functionCost : CostExpr) (source : Term)
  | append (left right : Term)
deriving Repr, DecidableEq

abbrev ValueEnv := String -> Option Value

def emptyValueEnv : ValueEnv := fun _ => none

def bindValue (env : ValueEnv) (name : String) (value : Value) : ValueEnv :=
  fun query => if query = name then some value else env query

/- Frames: Value Evaluation. -/
def Term.eval (env : ValueEnv) : Term -> Except String Value
  | .nat value => pure (.nat value)
  | .bool value => pure (.bool value)
  | .variable name =>
      match env name with
      | some value => pure value
      | none => throw s!"unbound variable: {name}"
  | .add left right => do
      match <- left.eval env, <- right.eval env with
      | .nat x, .nat y => pure (.nat (x + y))
      | _, _ => throw "add expects two natural numbers"
  | .ifThenElse condition thenBranch elseBranch => do
      match <- condition.eval env with
      | .bool true => thenBranch.eval env
      | .bool false => elseBranch.eval env
      | _ => throw "if expects a Boolean condition"
  | .list values => pure (.list values)
  | .listInput _ valueName =>
      match env valueName with
      | some (.list values) => pure (.list values)
      | some _ => throw s!"{valueName} is not a list"
      | none => throw s!"unbound list: {valueName}"
  | .mapAdd increment _ source => do
      match <- source.eval env with
      | .list values => pure (.list (values.map fun value => value + increment))
      | _ => throw "map expects a list"
  | .append left right => do
      match <- left.eval env, <- right.eval env with
      | .list leftValues, .list rightValues =>
          pure (.list (leftValues ++ rightValues))
      | _, _ => throw "append expects two lists"

/- Frames: Shape Interpretation.
   None means the term is not statically known to produce a list. -/
def Term.lengthExpr : Term -> Option CostExpr
  | .list values => some (.const values.length)
  | .listInput lengthName _ => some (.var lengthName)
  | .mapAdd _ _ source => source.lengthExpr
  | .append left right => do
      let leftLength <- left.lengthExpr
      let rightLength <- right.lengthExpr
      pure (.add leftLength rightLength)
  | _ => none

/- Frames: Cost Evaluation.
   This is an external interpretation: Term does not store an accumulated
   runtime cost. The analyzer constructs a separate CostExpr tree. -/
def Term.cost : Term -> Except String CostExpr
  | .nat _ => pure (.const 0)
  | .bool _ => pure (.const 0)
  | .variable _ => pure (.const 0)
  | .add left right => do
      let leftCost <- left.cost
      let rightCost <- right.cost
      pure (.add leftCost (.add rightCost (.const 1)))
  | .ifThenElse condition thenBranch elseBranch => do
      let conditionCost <- condition.cost
      let thenCost <- thenBranch.cost
      let elseCost <- elseBranch.cost
      pure (.add conditionCost (.add (.const 1) (.max thenCost elseCost)))
  | .list _ => pure (.const 0)
  | .listInput _ _ => pure (.const 0)
  | .mapAdd _ functionCost source => do
      let sourceCost <- source.cost
      match source.lengthExpr with
      | some length =>
          pure (.add sourceCost (.mul length functionCost))
      | none => throw "map source has no list-length interpretation"
  | .append left right => do
      let leftCost <- left.cost
      let rightCost <- right.cost
      match left.lengthExpr with
      | some leftLength =>
          pure (.add (.add leftCost rightCost) leftLength)
      | none => throw "append left side has no list-length interpretation"

theorem Term.eval_add_literals (left right : Nat) :
    (Term.add (.nat left) (.nat right)).eval emptyValueEnv =
      Except.ok (.nat (left + right)) := by
  rfl

theorem Term.map_input_cost
    (increment : Nat)
    (functionCost : CostExpr)
    (lengthName valueName : String) :
    (Term.mapAdd increment functionCost
      (.listInput lengthName valueName)).cost =
      Except.ok (.add (.const 0) (.mul (.var lengthName) functionCost)) := by
  rfl

theorem Term.append_inputs_cost
    (leftLength leftValue rightLength rightValue : String) :
    (Term.append
      (.listInput leftLength leftValue)
      (.listInput rightLength rightValue)).cost =
      Except.ok (.add (.add (.const 0) (.const 0)) (.var leftLength)) := by
  rfl

def sampleTerm : Term :=
  .ifThenElse
    (.bool true)
    (.mapAdd 1 (.const 2) (.listInput "n" "xs"))
    (.list [])

#eval sampleTerm.eval
  (bindValue emptyValueEnv "xs" (.list [10, 20, 30]))
#eval sampleTerm.cost
#eval CostExpr.eval
  (.mul (.var "n") (.const 2))
  (fun name => if name = "n" then 3 else 0)

end D6AutomaticComplexity
