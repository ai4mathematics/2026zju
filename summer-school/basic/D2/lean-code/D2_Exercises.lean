/-
  D2_Exercises.lean

  Guided exercises for D2. This file intentionally contains `sorry`.
  Students can replace each `sorry` during class or after class.
-/

namespace D2Exercises

/-! ## Exercise 1: an enumeration type -/

inductive TrafficLight where
  | red | yellow | green
  deriving Repr, BEq, DecidableEq

def shouldStop : TrafficLight -> Bool := by
  -- Fill in by cases on the traffic light.
  sorry

-- After solving the exercise, try:
-- #eval shouldStop TrafficLight.red
-- #eval shouldStop TrafficLight.green

/-! ## Exercise 2: Option -/

def optionToNat (default : Nat) : Option Nat -> Nat := by
  -- Return the number inside `some`; return `default` for `none`.
  sorry

-- After solving the exercise, try:
-- #eval optionToNat 0 (some 12)
-- #eval optionToNat 0 none

/-! ## Exercise 3: List recursion -/

def doubleAll : List Nat -> List Nat := by
  -- Double every number in a list.
  sorry

-- After solving the exercise, try:
-- #eval doubleAll [1, 2, 3]

def sumList : List Nat -> Nat := by
  -- Sum all numbers in a list.
  sorry

-- After solving the exercise, try:
-- #eval sumList [1, 2, 3, 4]

/-! ## Exercise 4: proof by cases -/

example (b : Bool) : b = true \/ b = false := by
  -- Try `cases b`.
  sorry

example (x : Option Nat) :
    x = none \/ Exists fun n => x = some n := by
  -- Try `cases x`.
  sorry

/-! ## Exercise 5: induction on lists -/

theorem append_nil_right_ex {alpha : Type} (xs : List alpha) :
    xs ++ [] = xs := by
  -- Try `induction xs`.
  sorry

theorem map_id_ex {alpha : Type} (xs : List alpha) :
    List.map (fun x => x) xs = xs := by
  -- Try `induction xs`.
  sorry

/-! ## Exercise 6: structures -/

structure Student where
  name : String
  score : Nat
  deriving Repr, BEq, DecidableEq

def addBonus (s : Student) (bonus : Nat) : Student := by
  -- Return a new student with the same name and increased score.
  sorry

/-! ## Exercise 7: type classes -/

class HasNorm (alpha : Type) where
  norm : alpha -> Nat

structure Vector2 where
  x : Int
  y : Int
  deriving Repr, BEq, DecidableEq

def intAbsNat (z : Int) : Nat :=
  if z < 0 then Int.toNat (-z) else Int.toNat z

instance : HasNorm Vector2 := by
  -- Define the norm as |x| + |y| using `intAbsNat`.
  sorry

def doubleNorm {alpha : Type} [HasNorm alpha] (x : alpha) : Nat :=
  2 * HasNorm.norm x

-- After solving the instance exercise, try:
-- #eval doubleNorm ({ x := -2, y := 3 } : Vector2)

/-! ## Exercise 8: expression trees -/

inductive Expr where
  | const : Nat -> Expr
  | add : Expr -> Expr -> Expr
  | var : String -> Expr
  deriving Repr, BEq, DecidableEq

namespace Expr

def vars : Expr -> List String := by
  -- Collect all variable names appearing in an expression.
  sorry

def mirror : Expr -> Expr := by
  -- Swap left and right subexpressions recursively.
  sorry

theorem mirror_mirror (e : Expr) :
    mirror (mirror e) = e := by
  -- Prove by induction on `e`.
  sorry

end Expr

end D2Exercises
