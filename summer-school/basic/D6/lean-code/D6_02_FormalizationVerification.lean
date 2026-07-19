import Std

set_option autoImplicit false

namespace D6FormalizationVerification

/- Frames: Scheme Interpreter as a Formalization /
   This is a deliberately small local analogue of the D5 project and the
   cited Haskell repository. Parsing, macros, and closures are later layers. -/
inductive SExpr where
  | int (value : Int)
  | bool (value : Bool)
  | symbol (name : String)
  | add (left right : SExpr)
  | ifThenElse (condition thenBranch elseBranch : SExpr)
deriving Repr, DecidableEq

inductive SVal where
  | int (value : Int)
  | bool (value : Bool)
deriving Repr, DecidableEq

abbrev Env := String -> Option SVal

def emptyEnv : Env := fun _ => none

def bindValue (env : Env) (name : String) (value : SVal) : Env :=
  fun query => if query = name then some value else env query

def eval (env : Env) : SExpr -> Except String SVal
  | .int n => pure (.int n)
  | .bool b => pure (.bool b)
  | .symbol name =>
      match env name with
      | some value => pure value
      | none => throw s!"unbound symbol: {name}"
  | .add left right => do
      let leftValue <- eval env left
      let rightValue <- eval env right
      match leftValue, rightValue with
      | .int x, .int y => pure (.int (x + y))
      | _, _ => throw "addition expects two integers"
  | .ifThenElse condition thenBranch elseBranch => do
      match <- eval env condition with
      | .bool true => eval env thenBranch
      | .bool false => eval env elseBranch
      | _ => throw "if expects a Boolean condition"

theorem eval_add_literals (x y : Int) :
    eval emptyEnv (.add (.int x) (.int y)) = .ok (.int (x + y)) := by
  rfl

theorem eval_bound_symbol (name : String) (value : SVal) :
    eval (bindValue emptyEnv name value) (.symbol name) = .ok value := by
  simp only [eval, bindValue, if_pos]
  change (Except.ok value : Except String SVal) = Except.ok value
  rfl

/- Frames: A Familiar Game as a State Machine.
   A move removes one or two stones. A successful transition changes the turn
   and strictly decreases the number of stones. -/
inductive Player where
  | alice
  | bob
deriving Repr, DecidableEq

def Player.other : Player -> Player
  | .alice => .bob
  | .bob => .alice

inductive Take where
  | one
  | two
deriving Repr, DecidableEq

def Take.amount : Take -> Nat
  | .one => 1
  | .two => 2

structure TakeState where
  stones : Nat
  turn : Player
deriving Repr, DecidableEq

def legalTake (state : TakeState) (move : Take) : Bool :=
  decide (move.amount <= state.stones)

def takeStep (state : TakeState) (move : Take) : Option TakeState :=
  if legalTake state move then
    some {
      stones := state.stones - move.amount
      turn := state.turn.other
    }
  else
    none

theorem take_two_from_three :
    takeStep { stones := 3, turn := .alice } .two =
      some { stones := 1, turn := .bob } := by
  rfl

theorem successful_take_decreases
    (state next : TakeState)
    (move : Take)
    (successful : takeStep state move = some next) :
    next.stones < state.stones := by
  unfold takeStep at successful
  split at successful
  · cases successful
    cases move <;> simp_all [legalTake, Take.amount]
    all_goals omega
  · contradiction

/- Frames: A Tiny Learning Example.
   The paper uses real-valued functions and probability measures. This Boolean
   model only teaches the words classifier, sample, and empirical error. -/
structure LabeledBool where
  input : Bool
  label : Bool
deriving Repr, DecidableEq

structure TinyClassifier where
  predict : Bool -> Bool

def mistake (classifier : TinyClassifier) (samplePoint : LabeledBool) : Nat :=
  if classifier.predict samplePoint.input = samplePoint.label then 0 else 1

def empiricalMistakes (classifier : TinyClassifier) :
    List LabeledBool -> Nat
  | [] => 0
  | samplePoint :: rest =>
      mistake classifier samplePoint + empiricalMistakes classifier rest

def identityClassifier : TinyClassifier where
  predict := fun input => input

def tinySample : List LabeledBool :=
  [{ input := false, label := false }, { input := true, label := true }]

theorem identityClassifier_zero_mistakes :
    empiricalMistakes identityClassifier tinySample = 0 := by
  rfl

/- Frames: Explicit Parameters in a Mathematical Formalization /
   This small interface mirrors the dependency shape of a learning-theory
   theorem without pretending to reproduce its measure-theoretic content. -/
structure LearningProblem (Sample Hypothesis : Type) where
  empiricalRisk : Hypothesis -> List Sample -> Nat
  populationRisk : Hypothesis -> Nat

def Generalizes
    (Sample Hypothesis : Type)
    (problem : LearningProblem Sample Hypothesis)
    (data : List Sample)
    (epsilon : Nat) : Prop :=
  forall h, problem.populationRisk h <= problem.empiricalRisk h data + epsilon

theorem generalizes_from_two_lemmas
    (Sample Hypothesis : Type)
    (problem : LearningProblem Sample Hypothesis)
    (data : List Sample)
    (middle : Hypothesis -> Nat)
    (epsilonOne epsilonTwo : Nat)
    (populationToMiddle :
      forall h, problem.populationRisk h <= middle h + epsilonOne)
    (middleToEmpirical :
      forall h, middle h <= problem.empiricalRisk h data + epsilonTwo) :
    Generalizes Sample Hypothesis problem data (epsilonOne + epsilonTwo) := by
  intro h
  have hOne := populationToMiddle h
  have hTwo := middleToEmpirical h
  omega

/- Frames: A Small Local Interface and @[ext] /
   The proof field records only a minimal invariant. A real bridge theorem
   would construct this structure from a Mathlib PMF or probability measure. -/
@[ext]
structure FiniteLaw (Outcome : Type) where
  mass : Outcome -> Nat
  total : Nat
  positive : 0 < total

theorem FiniteLaw.eq_of_fields
    (Outcome : Type)
    (left right : FiniteLaw Outcome)
    (massEq : left.mass = right.mass)
    (totalEq : left.total = right.total) :
    left = right := by
  cases left
  cases right
  simp_all

/- Frames: Build a Bridge Between Two Representations.
   LibraryLaw is a dependency-free stand-in. In a full project, replace it
   with a Mathlib PMF or finite probability measure and prove the same two
   round-trip laws. -/
@[ext]
structure LibraryLaw (Outcome : Type) where
  mass : Outcome -> Nat
  total : Nat
  positive : 0 < total

structure SimpleEquiv (Left Right : Type) where
  toFun : Left -> Right
  invFun : Right -> Left
  left_inv : forall value, invFun (toFun value) = value
  right_inv : forall value, toFun (invFun value) = value

instance {Left Right : Type} :
    CoeFun (SimpleEquiv Left Right) (fun _ => Left -> Right) where
  coe equivalence := equivalence.toFun

def SimpleEquiv.symm {Left Right : Type}
    (equivalence : SimpleEquiv Left Right) : Right -> Left :=
  equivalence.invFun

def finiteLawEquiv (Outcome : Type) :
    SimpleEquiv (FiniteLaw Outcome) (LibraryLaw Outcome) where
  toFun law :=
    { mass := law.mass, total := law.total, positive := law.positive }
  invFun law :=
    { mass := law.mass, total := law.total, positive := law.positive }
  left_inv law := by
    cases law
    rfl
  right_inv law := by
    cases law
    rfl

/- Frames: CompCert Pattern on a Tiny Compiler /
   SrcExpr and Instr are the formal systems. compile is the implementation.
   compile_correct is verification relative to evalSrc and exec. -/
inductive SrcExpr where
  | lit (value : Nat)
  | add (left right : SrcExpr)
deriving Repr, DecidableEq

inductive Instr where
  | push (value : Nat)
  | add
deriving Repr, DecidableEq

def evalSrc : SrcExpr -> Nat
  | .lit value => value
  | .add left right => evalSrc left + evalSrc right

def exec : List Instr -> List Nat -> Option (List Nat)
  | [], stack => some stack
  | .push value :: code, stack => exec code (value :: stack)
  | .add :: code, right :: left :: stack => exec code ((left + right) :: stack)
  | .add :: _, _ => none

def compile : SrcExpr -> List Instr
  | .lit value => [.push value]
  | .add left right => compile left ++ compile right ++ [.add]

theorem exec_append (first second : List Instr) (stack : List Nat) :
    exec (first ++ second) stack =
      match exec first stack with
      | none => none
      | some nextStack => exec second nextStack := by
  induction first generalizing stack with
  | nil => rfl
  | cons instruction first inductionHypothesis =>
      cases instruction with
      | push value =>
          simp [exec, inductionHypothesis]
      | add =>
          cases stack with
          | nil => rfl
          | cons right stack =>
              cases stack with
              | nil => rfl
              | cons left stack =>
                  simp [exec, inductionHypothesis]

theorem compile_correct (expression : SrcExpr) (stack : List Nat) :
    exec (compile expression) stack = some (evalSrc expression :: stack) := by
  induction expression generalizing stack with
  | lit value =>
      rfl
  | add left right leftHypothesis rightHypothesis =>
      simp [compile, exec_append, leftHypothesis, rightHypothesis, exec, evalSrc]

#eval eval emptyEnv (.add (.int 20) (.int 22))
#eval eval (bindValue emptyEnv "x" (.int 7)) (.symbol "x")
#eval takeStep { stones := 3, turn := .alice } .two
#eval takeStep { stones := 1, turn := .bob } .two
#eval empiricalMistakes identityClassifier tinySample
#eval compile (.add (.lit 20) (.lit 22))
#eval exec (compile (.add (.lit 20) (.lit 22))) []

end D6FormalizationVerification

open D6FormalizationVerification

/- Frames: One SExpr Run Before More Definitions. -/
def main : IO Unit := do
  let expression :=
    SExpr.ifThenElse (.bool false) (.int 10) (.int 20)
  let result := eval emptyEnv expression
  IO.println s!"expression = {reprStr expression}"
  IO.println s!"result = {reprStr result}"
