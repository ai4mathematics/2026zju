-- D5_01: Local code for the first programming block.
-- Frames: "Example: The Factorial Function" through "Break 1: List and Recursion Checkpoint".

-- Frame: Functional Translation / Why Is This Recursive Definition Allowed?
def fact : Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

#eval fact 5

-- Frames: List Function 0 and its solution.
def add2 : Nat -> Nat
  | .zero => .succ (.succ .zero)
  | .succ k => .succ (.succ (.succ k))

def add : Nat -> Nat -> Nat
  | .zero, n => n
  | .succ k, n => .succ (add k n)

def mul : Nat -> Nat -> Nat
  | _, .zero => .zero
  | m, .succ k => add m (mul m k)

#eval add 3 4
#eval mul 3 4

-- Frame: Solution to List Function 1.
def myHead : List a -> Option a
  | [] => none
  | x :: _ => some x

def myLength : List a -> Nat
  | [] => 0
  | _ :: xs => myLength xs + 1

def myTake : Nat -> List a -> List a
  | 0, _ => []
  | _, [] => []
  | n + 1, x :: xs => x :: myTake n xs

def myTail : List a -> List a
  | [] => []
  | _ :: xs => xs

def myDrop : Nat -> List a -> List a
  | 0, xs => xs
  | _, [] => []
  | n + 1, _ :: xs => myDrop n xs

#eval myHead [1, 2, 3]
#eval myLength [1, 2, 3, 4]
#eval myTake 3 [10, 20, 30, 40, 50]
#eval myTail [10, 20, 30]
#eval myDrop 2 [10, 20, 30, 40]

-- Frames: List Function 2 and map.
def add1 : List Nat -> List Nat
  | [] => []
  | x :: xs => (x + 1) :: add1 xs

def mul2 : List Nat -> List Nat
  | [] => []
  | x :: xs => (x * 2) :: mul2 xs

def applyF (f : Nat -> Nat) : List Nat -> List Nat
  | [] => []
  | x :: xs => f x :: applyF f xs

def myMap (f : a -> b) : List a -> List b
  | [] => []
  | x :: xs => f x :: myMap f xs

def myAppend : List a -> List a -> List a
  | [], ys => ys
  | x :: xs, ys => x :: myAppend xs ys

def revAcc (acc : List a) : List a -> List a
  | [] => acc
  | x :: xs => revAcc (x :: acc) xs

def myReverse (xs : List a) : List a :=
  revAcc [] xs

#eval add1 [1, 2, 3]
#eval mul2 [1, 2, 3]
#eval applyF (fun n => n * n) [1, 2, 3]
#eval myMap (fun n => n - 1) [3, 4, 5]
#eval myAppend [1, 2] [3, 4]
#eval myReverse [1, 2, 3, 4]

-- Frames: List Function 4 and foldr.
def sumlst : List Nat -> Nat :=
  let rec loop : List Nat -> Nat -> Nat
    | [], acc => acc
    | x :: xs, acc => loop xs (acc + x)
  fun lst => loop lst 0

def prodlst : List Nat -> Nat :=
  let rec loop : List Nat -> Nat -> Nat
    | [], acc => acc
    | x :: xs, acc => loop xs (acc * x)
  fun lst => loop lst 1

def myFoldr (f : a -> b -> b) (init : b) : List a -> b
  | [] => init
  | x :: xs => f x (myFoldr f init xs)

def sumSquares : List Nat -> Nat :=
  myFoldr (fun x acc => x * x + acc) 0

def myFilter (p : a -> Bool) : List a -> List a
  | [] => []
  | x :: xs =>
      if p x then x :: myFilter p xs else myFilter p xs

#eval sumlst [1, 2, 3, 4]
#eval prodlst [1, 2, 3, 4]
#eval sumSquares [1, 2, 3, 4]
#eval myFilter (fun n => n % 2 == 0) [1, 2, 3, 4, 5, 6]

-- Exercises for class:
-- Frame: Exercise: Merge Sort in Lean 4 / Break 1.
-- 1. Re-derive myTail and myDrop before looking back at the code.
-- 2. Write a variant of myFilter that keeps only numbers in a chosen interval.
-- 3. Compare the direct-recursive and fold-based versions of a list sum.
