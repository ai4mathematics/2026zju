import Std

set_option autoImplicit false

namespace D6TimeMReference

/- Slides: the local TimeM implementation used in the complexity project is
   the same result/cost shape as current CSLib's TimeM API. -/
structure TimeM (Time : Type) (Alpha : Type) where
  ret : Alpha
  time : Time

variable {Time : Type}

instance [Zero Time] [Add Time] : Monad (TimeM Time) where
  pure value := { ret := value, time := 0 }
  bind computation next :=
    let result := next computation.ret
    { ret := result.ret, time := computation.time + result.time }

def tick (cost : Time) : TimeM Time PUnit :=
  { ret := PUnit.unit, time := cost }

def insertM (x : Nat) (xs : List Nat) : TimeM Nat (List Nat) :=
  match xs with
  | [] => pure [x]
  | y :: ys => do
      let _ <- tick 1
      if x <= y then
        pure (x :: y :: ys)
      else
        let rest <- insertM x ys
        pure (y :: rest)

def getCost {α : Type} (comp : TimeM Nat α) : Nat := comp.time

def getResult {α : Type} (comp : TimeM Nat α) : α := comp.ret

#eval getCost (insertM 5 [1, 2, 3, 4])
#eval getResult (insertM 5 [1, 2, 3, 4])

end D6TimeMReference
