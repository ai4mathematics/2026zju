/-
  D2_Exercises_Solutions.lean

  Instructor solution file for D2_Exercises.lean.
  The solutions are intentionally written in a direct style suitable for class.
-/

namespace D2ExercisesSolutions

/-! ## Exercise 1: an enumeration type -/

inductive TrafficLight where
  | red | yellow | green
  deriving Repr, BEq, DecidableEq

def shouldStop : TrafficLight -> Bool
  | TrafficLight.red => true
  | TrafficLight.yellow => true
  | TrafficLight.green => false

#eval shouldStop TrafficLight.red
#eval shouldStop TrafficLight.green

/-! ## Exercise 2: Option -/

def optionToNat (default : Nat) : Option Nat -> Nat
  | none => default
  | some n => n

#eval optionToNat 0 (some 12)
#eval optionToNat 0 none

/-! ## Exercise 3: List recursion -/

def doubleAll : List Nat -> List Nat
  | [] => []
  | x :: xs => (2 * x) :: doubleAll xs

#eval doubleAll [1, 2, 3]

def sumList : List Nat -> Nat
  | [] => 0
  | x :: xs => x + sumList xs

#eval sumList [1, 2, 3, 4]

/-! ## Exercise 4: proof by cases -/

example (b : Bool) : b = true \/ b = false := by
  cases b
  · exact Or.inr rfl
  · exact Or.inl rfl

example (x : Option Nat) :
    x = none \/ Exists fun n => x = some n := by
  cases x with
  | none =>
      exact Or.inl rfl
  | some n =>
      exact Or.inr (Exists.intro n rfl)

/-! ## Exercise 5: induction on lists -/

theorem append_nil_right_ex {alpha : Type} (xs : List alpha) :
    xs ++ [] = xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      calc
        (x :: xs) ++ [] = x :: (xs ++ []) := rfl
        _ = x :: xs := by rw [ih]

theorem map_id_ex {alpha : Type} (xs : List alpha) :
    List.map (fun x => x) xs = xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [ih]

/-! ## Exercise 6: structures -/

structure Student where
  name : String
  score : Nat
  deriving Repr, BEq, DecidableEq

def addBonus (s : Student) (bonus : Nat) : Student :=
  { s with score := s.score + bonus }

#eval addBonus { name := "Ada", score := 90 } 5

/-! ## Exercise 7: type classes -/

class HasNorm (alpha : Type) where
  norm : alpha -> Nat

structure Vector2 where
  x : Int
  y : Int
  deriving Repr, BEq, DecidableEq

def intAbsNat (z : Int) : Nat :=
  if z < 0 then Int.toNat (-z) else Int.toNat z

instance : HasNorm Vector2 where
  norm v := intAbsNat v.x + intAbsNat v.y

def doubleNorm {alpha : Type} [HasNorm alpha] (x : alpha) : Nat :=
  2 * HasNorm.norm x

#eval doubleNorm ({ x := -2, y := 3 } : Vector2)

/-! ## Exercise 8: expression trees -/

inductive Expr where
  | const : Nat -> Expr
  | add : Expr -> Expr -> Expr
  | var : String -> Expr
  deriving Repr, BEq, DecidableEq

namespace Expr

def vars : Expr -> List String
  | const _ => []
  | add left right => vars left ++ vars right
  | var name => [name]

def mirror : Expr -> Expr
  | const n => const n
  | add left right => add (mirror right) (mirror left)
  | var name => var name

theorem mirror_mirror (e : Expr) :
    mirror (mirror e) = e := by
  induction e with
  | const n =>
      rfl
  | add left right ihLeft ihRight =>
      simp [mirror, ihLeft, ihRight]
  | var name =>
      rfl

end Expr

end D2ExercisesSolutions
