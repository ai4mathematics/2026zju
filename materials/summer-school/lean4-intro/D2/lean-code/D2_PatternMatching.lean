/-
  D2_PatternMatching.lean

  Live demo file for pattern matching and structural recursion.
-/

namespace D2PatternMatching

/-! ## Matching on an enumeration -/

inductive Weekday where
  | mon | tue | wed | thu | fri | sat | sun
  deriving Repr, BEq, DecidableEq

def isWeekend : Weekday -> Bool
  | Weekday.sat => true
  | Weekday.sun => true
  | _ => false

#eval isWeekend Weekday.mon
#eval isWeekend Weekday.sat

def nextWeekday : Weekday -> Weekday
  | Weekday.mon => Weekday.tue
  | Weekday.tue => Weekday.wed
  | Weekday.wed => Weekday.thu
  | Weekday.thu => Weekday.fri
  | Weekday.fri => Weekday.sat
  | Weekday.sat => Weekday.sun
  | Weekday.sun => Weekday.mon

#eval nextWeekday Weekday.fri
#eval nextWeekday Weekday.sun

/-! ## Matching on Option -/

def getWithDefault {alpha : Type} (default : alpha) : Option alpha -> alpha
  | none => default
  | some a => a

#eval getWithDefault 0 (some 37)
#eval getWithDefault 0 (none : Option Nat)

def optionMap {alpha beta : Type} (f : alpha -> beta) :
    Option alpha -> Option beta
  | none => none
  | some a => some (f a)

#eval optionMap (fun n : Nat => n + 1) (some 4)
#eval optionMap (fun n : Nat => n + 1) none

/-! ## Matching on lists -/

def safeHead {alpha : Type} : List alpha -> Option alpha
  | [] => none
  | x :: _ => some x

#eval safeHead [10, 20, 30]
#eval safeHead ([] : List Nat)

def isEmpty {alpha : Type} : List alpha -> Bool
  | [] => true
  | _ :: _ => false

#eval isEmpty ([] : List Nat)
#eval isEmpty [1, 2, 3]

/-! ## Structural recursion on natural numbers -/

def add (m : Nat) : Nat -> Nat
  | 0 => m
  | n + 1 => add m n + 1

def mul (m : Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 => mul m n + m

def pow (m : Nat) : Nat -> Nat
  | 0 => 1
  | n + 1 => pow m n * m

#eval add 3 4
#eval mul 3 4
#eval pow 2 5

/-!
These definitions recurse on the second argument.
They mirror familiar mathematical equations:

  m + 0       = m
  m + (n + 1) = (m + n) + 1

and similarly for multiplication and powers.
-/

/-! ## Structural recursion on lists -/

def myLength {alpha : Type} : List alpha -> Nat
  | [] => 0
  | _ :: xs => myLength xs + 1

#eval myLength ([] : List Nat)
#eval myLength [4, 5, 6]

def myMap {alpha beta : Type} (f : alpha -> beta) :
    List alpha -> List beta
  | [] => []
  | x :: xs => f x :: myMap f xs

#eval myMap (fun n : Nat => n + 10) [1, 2, 3]

def myAppend {alpha : Type} : List alpha -> List alpha -> List alpha
  | [], ys => ys
  | x :: xs, ys => x :: myAppend xs ys

#eval myAppend [1, 2] [3, 4]

def sumList : List Nat -> Nat
  | [] => 0
  | x :: xs => x + sumList xs

#eval sumList [1, 2, 3, 4]

/-! ## Structural recursion on trees -/

inductive Tree (alpha : Type) where
  | leaf : alpha -> Tree alpha
  | node : Tree alpha -> Tree alpha -> Tree alpha
  deriving Repr, BEq

def treeSize {alpha : Type} : Tree alpha -> Nat
  | Tree.leaf _ => 1
  | Tree.node left right => treeSize left + treeSize right + 1

def treeLeaves {alpha : Type} : Tree alpha -> Nat
  | Tree.leaf _ => 1
  | Tree.node left right => treeLeaves left + treeLeaves right

def sampleTree : Tree Nat :=
  Tree.node (Tree.leaf 10) (Tree.node (Tree.leaf 20) (Tree.leaf 30))

#eval treeSize sampleTree
#eval treeLeaves sampleTree

/-!
Exercise ideas:
1. Define factorial by recursion on natural numbers.
2. Define a function that doubles every natural number in a list.
3. Define a function that counts the number of leaves in a tree.
4. For each recursive call, identify which argument became smaller.
-/

end D2PatternMatching
