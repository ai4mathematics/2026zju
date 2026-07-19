import Std

set_option autoImplicit false

namespace D6ComplexityProof

/- Frames: The TimeM/Tick Pattern.
   This local definition mirrors the public shape of CSLib's current TimeM so
   the lecture remains runnable without an online dependency. -/
structure TimeM (T : Type) (Alpha : Type) where
  ret : Alpha
  time : T

variable {T Alpha Beta : Type}

instance [Zero T] [Add T] : Monad (TimeM T) where
  pure value := { ret := value, time := 0 }
  bind computation next :=
    let result := next computation.ret
    { ret := result.ret, time := computation.time + result.time }

def tick (cost : T) : TimeM T PUnit :=
  { ret := PUnit.unit, time := cost }

def constantWork (cost : Nat) (value : Alpha) : TimeM Nat Alpha := do
  let _ <- tick cost
  pure value

@[simp]
theorem constantWork_ret_value (cost : Nat) (value : Alpha) :
    (constantWork cost value).ret = value := by
  rfl

def timedMap (function : Alpha -> TimeM Nat Beta) :
    List Alpha -> TimeM Nat (List Beta)
  | [] => { ret := [], time := 0 }
  | head :: tail =>
      let first := function head
      let rest := timedMap function tail
      { ret := first.ret :: rest.ret, time := first.time + rest.time }

theorem timedMap_time
    (function : Alpha -> TimeM Nat Beta)
    (cost : Nat)
    (constantCost : forall value, (function value).time = cost)
    (input : List Alpha) :
    (timedMap function input).time = input.length * cost := by
  induction input with
  | nil =>
      simp [timedMap]
  | cons head tail inductionHypothesis =>
      simp [timedMap, constantCost head, inductionHypothesis,
        Nat.add_mul, Nat.add_comm]

theorem timedMap_constantWork_ret
    (cost : Nat)
    (input : List Alpha) :
    (timedMap (constantWork cost) input).ret = input := by
  induction input with
  | nil =>
      rfl
  | cons head tail inductionHypothesis =>
      simp [timedMap, constantWork_ret_value, inductionHypothesis]

theorem timedMap_three_items :
    (timedMap (constantWork 2) [10, 20, 30]).time = 6 := by
  rfl

/- Frames: CSLib Timed Merge Sort.
   The charged operation is comparison of two nonempty heads. Constructors,
   splitting, and function calls are free in this model. -/
def merge : List Nat -> List Nat -> TimeM Nat (List Nat)
  | [], right => { ret := right, time := 0 }
  | left, [] => { ret := left, time := 0 }
  | leftHead :: leftTail, rightHead :: rightTail =>
      if leftHead <= rightHead then
        let rest := merge leftTail (rightHead :: rightTail)
        { ret := leftHead :: rest.ret, time := 1 + rest.time }
      else
        let rest := merge (leftHead :: leftTail) rightTail
        { ret := rightHead :: rest.ret, time := 1 + rest.time }
termination_by left right => left.length + right.length

theorem merge_time_le :
    forall left right,
      (merge left right).time <= left.length + right.length
  | [], right => by
      simp [merge]
  | left, [] => by
      cases left <;> simp [merge]
  | leftHead :: leftTail, rightHead :: rightTail => by
      simp only [merge]
      split
      · have inductionHypothesis :=
          merge_time_le leftTail (rightHead :: rightTail)
        simp only [List.length_cons] at inductionHypothesis ⊢
        omega
      · have inductionHypothesis :=
          merge_time_le (leftHead :: leftTail) rightTail
        simp only [List.length_cons] at inductionHypothesis ⊢
        omega

/- This is the recurrence used by current CSLib. The complete CSLib proof
   connects program time to this recurrence and then proves an n*clog(2,n)
   upper bound with Mathlib's logarithm lemmas. -/
def timeMergeSortRec : Nat -> Nat
  | 0 => 0
  | 1 => 0
  | n + 2 =>
      timeMergeSortRec ((n + 2) / 2) +
      timeMergeSortRec (((n + 2) - 1) / 2 + 1) +
      (n + 2)

def mergeSortUpper (n : Nat) : Nat :=
  n * (Nat.log2 n + 1)

theorem timeMergeSortRec_two : timeMergeSortRec 2 = 2 := by
  native_decide

theorem mergeSortUpper_zero : mergeSortUpper 0 = 0 := by
  simp [mergeSortUpper]

/- Frames: From a Pointwise Bound to Big-O.
   This small Nat-only relation is for local exercises. Mathlib's real API is
   Asymptotics.IsBigO along a filter such as Filter.atTop. -/
def EventuallyAtTop (property : Nat -> Prop) : Prop :=
  exists threshold, forall n, threshold <= n -> property n

def IsBigO (function comparison : Nat -> Nat) : Prop :=
  exists constant,
    0 < constant /\
    EventuallyAtTop (fun n => function n <= constant * comparison n)

theorem pointwise_isBigO
    (function comparison : Nat -> Nat)
    (constant : Nat)
    (constantPositive : 0 < constant)
    (pointwise : forall n, function n <= constant * comparison n) :
    IsBigO function comparison := by
  refine ⟨constant, constantPositive, 0, ?_⟩
  intro n _
  exact pointwise n

theorem mergeSortUpper_isBigO :
    IsBigO mergeSortUpper mergeSortUpper := by
  apply pointwise_isBigO mergeSortUpper mergeSortUpper 1
  · decide
  · intro n
    simp

#eval (constantWork 3 "result").time
#eval (timedMap (constantWork 2) [10, 20, 30]).time
#eval (merge [1, 3, 5] [2, 4, 6]).ret
#eval (merge [1, 3, 5] [2, 4, 6]).time
#eval timeMergeSortRec 8

end D6ComplexityProof
