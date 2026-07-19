import Std

set_option autoImplicit false

namespace D6ComplexityProofExercises

/- Frames: TimeM and Big-O Exercises. This file is complete by itself. -/

structure TimeM (Time : Type) (Alpha : Type) where
  ret : Alpha
  time : Time

variable {Time Alpha : Type}

instance [Zero Time] [Add Time] : Monad (TimeM Time) where
  pure value := { ret := value, time := 0 }
  bind computation next :=
    let result := next computation.ret
    { ret := result.ret, time := computation.time + result.time }

def tick (cost : Time) : TimeM Time PUnit :=
  { ret := PUnit.unit, time := cost }

def constantWork (cost : Nat) (value : Alpha) : TimeM Nat Alpha := do
  let _ <- tick cost
  pure value

/- Frames: First Understand Plain Merge and Second-Break Practice.
   Comparing two nonempty heads costs one unit. -/

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

def EventuallyAtTop (property : Nat -> Prop) : Prop :=
  exists threshold, forall n, threshold <= n -> property n

def IsBigO (function comparison : Nat -> Nat) : Prop :=
  exists constant,
    0 < constant /\
    EventuallyAtTop (fun n => function n <= constant * comparison n)

/- Separate return-value claims from time claims before filling the holes. -/

theorem tick_time (cost : Nat) :
    (tick cost : TimeM Nat PUnit).time = cost := by
  sorry

theorem constantWork_ret (cost value : Nat) :
    (constantWork cost value).ret = value := by
  sorry

theorem merge_small_ret :
    (merge [1, 4] [2, 3]).ret = [1, 2, 3, 4] := by
  sorry

theorem merge_small_time :
    (merge [1, 4] [2, 3]).time = 3 := by
  sorry

theorem pointwise_linear_isBigO
    (function : Nat -> Nat)
    (constant : Nat)
    (constantPositive : 0 < constant)
    (bound : forall n, function n <= constant * n) :
    IsBigO function (fun n => n) := by
  sorry

end D6ComplexityProofExercises
