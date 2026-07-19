-- D5_01 exercises: easy Nat and List functions.
-- Fill these during class if time is short. The harder merge-sort challenge is
-- intentionally not included here.

-- Frame: List Function 0: write some Nat function.
def exAdd2 : Nat -> Nat
  | .zero => by
      sorry
  | .succ k => by
      sorry

def exAdd : Nat -> Nat -> Nat
  | .zero, n => by
      sorry
  | .succ k, n => by
      sorry

-- Optional if add is already comfortable.
def exMul : Nat -> Nat -> Nat
  | _, .zero => by
      sorry
  | m, .succ k => by
      sorry

-- Frame: List Function 1: basic tools.
def exHead : List a -> Option a
  | [] => by
      sorry
  | x :: _ => by
      sorry

def exLength : List a -> Nat
  | [] => by
      sorry
  | _ :: xs => by
      sorry

def exTake : Nat -> List a -> List a
  | 0, _ => by
      sorry
  | _, [] => by
      sorry
  | n + 1, x :: xs => by
      sorry

def exTail : List a -> List a
  | [] => by
      sorry
  | _ :: xs => by
      sorry

def exDrop : Nat -> List a -> List a
  | 0, xs => by
      sorry
  | _, [] => by
      sorry
  | n + 1, _ :: xs => by
      sorry

-- Frames: List Function 2 and List Function 5.
def exMap (f : a -> b) : List a -> List b
  | [] => by
      sorry
  | x :: xs => by
      sorry

def exFilter (p : a -> Bool) : List a -> List a
  | [] => by
      sorry
  | x :: xs => by
      sorry

