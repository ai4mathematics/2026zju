/-
  Lean examples linked from session01_lean_intro_slides.pptx.
  Click a code block in the PPT to jump to the corresponding section.
  Some snippets intentionally contain `sorry` because they are exercises.
-/

import Mathlib

set_option autoImplicit false

-- SLIDE 01 BLOCK 01
namespace S01B01

#check Nat
#eval 2 + 3

example (P : Prop) : P -> P := by
  intro h
  exact h

end S01B01

-- SLIDE 31 BLOCK 02
namespace S31B02

#check Nat
#check 37
#eval 2 + 3

end S31B02

-- SLIDE 32 BLOCK 03
namespace S32B03

#check 2
-- 2 : Nat

#check Nat
-- Nat : Type

end S32B03

-- SLIDE 33 BLOCK 04
namespace S33B04

#check Nat
#check 37
#check "hello"
#check true

end S33B04

-- SLIDE 34 BLOCK 05
namespace S34B05

def double (n : Nat) : Nat :=
  n + n

#check double
#eval double 21

end S34B05

-- SLIDE 35 BLOCK 06
namespace S35B06

#check fun x : Nat => x + 1

def applyTwice (f : Nat -> Nat) (x : Nat) : Nat :=
  f (f x)

#eval applyTwice (fun n => n + 1) 10

end S35B06

-- SLIDE 36 BLOCK 07
namespace S36B07

def add3 (a b c : Nat) : Nat :=
  a + b + c

#check add3
#check add3 1
#check add3 1 2
#check add3 1 2 3

end S36B07

-- SLIDE 37 BLOCK 08
namespace S37B08

def myConst {A B : Type} (a : A) (_ : B) : A :=
  a

#eval myConst 5 "ignored"

end S37B08

-- SLIDE 41 BLOCK 09
namespace S41B09

example (P Q : Prop) : P -> Q -> And P Q := by
  intro hP
  intro hQ
  exact And.intro hP hQ

#check And.intro
-- And.intro : P -> Q -> P /\ Q

end S41B09

-- SLIDE 42 BLOCK 10
namespace S42B10

example (P : Prop) (h : P) : P := by
  exact h

end S42B10

-- SLIDE 43 BLOCK 11
namespace S43B11

example (P : Prop) : P -> P := by
  intro h
  exact h

end S43B11

-- SLIDE 44 BLOCK 12
namespace S44B12

example (P Q : Prop) (hPQ : P -> Q) (hP : P) : Q := by
  apply hPQ
  exact hP

end S44B12

-- SLIDE 45 BLOCK 13
namespace S45B13

example (P Q : Prop) (hP : P) (hQ : Q) : And P Q := by
  constructor
  exact hP
  exact hQ

end S45B13

-- SLIDE 46 BLOCK 14
namespace S46B14

example (P Q : Prop) : Or P Q -> Or Q P := by
  intro h
  cases h with
  | inl hP => exact Or.inr hP
  | inr hQ => exact Or.inl hQ

end S46B14

-- SLIDE 47 BLOCK 15
namespace S47B15

example (P : Prop) (hP : P) (hNotP : Not  P) : False := by
  contradiction

example (P : Prop) (hP : P) (hNotP : P -> False) : False := by
  contradiction

end S47B15

-- SLIDE 48 BLOCK 16
namespace S48B16

example (m : Nat) : Exists (fun n : Nat => 0 + n = m) := by
  use m
  simp

end S48B16

-- SLIDE 49 BLOCK 17
namespace S49B17

example (a : Nat) : a + 0 = a := by
  rfl

example (a : Nat) : 0 + a = a := by
  exact Nat.zero_add a

end S49B17

-- SLIDE 50 BLOCK 18
namespace S50B18

example (a b c : Nat) (h : a = b) : a + c = b + c := by
  rw [h]

example (a b c : Nat) (h : a = b) : c + b = c + a := by
  rw [h.symm]

end S50B18

-- SLIDE 51 BLOCK 19
namespace S51B19

example (a : Nat) : a + 0 = a := by
  simp

def square (n : Nat) : Nat :=
  n * n

example : square 3 = 9 := by
  simp [square]

end S51B19

-- SLIDE 53 BLOCK 20
namespace S53B20

#check Nat
#eval 2 + 3

def double (n : Nat) : Nat := n + n
#eval double 21

example (P : Prop) : P -> P := by
  intro h
  exact h

end S53B20

-- SLIDE 55 BLOCK 21
namespace S55B21

example (P Q R : Prop) :
    (P -> Q) -> (Q -> R) -> P -> R := by
  sorry

example (a b : Nat) (h : a = b) : a + a = b + b := by
  sorry

end S55B21

-- SLIDE 32A BLOCK 22
namespace S32AB22

#check 42
#check "hello"
#check true
#check Nat
#check Type

-- Expected error:
-- #check 42 + "hi"

end S32AB22

-- SLIDE 32B BLOCK 23
namespace S32BB23

#check Nat
#check Bool
#check Prop
#check Type
#check Type 1

#check Type -> Type
#check Type × Type

end S32BB23

-- SLIDE 32C BLOCK 24
namespace S32CB24

#check ((n : Nat) -> Fin (n + 1))
#check (∀ n : Nat, n = n)

example : ((n : Nat) -> Fin (n + 1)) :=
  fun n => ⟨0, Nat.succ_pos n⟩

example : (∀ n : Nat, n = n) := by
  intro n
  rfl

end S32CB24

-- SLIDE 49A BLOCK 25
namespace S49AB25

def onePlusOne : Nat := 1 + 1

#reduce (fun n : Nat => n + 1) 3
#reduce 2 + 3
#reduce onePlusOne
#check onePlusOne
#print onePlusOne

end S49AB25

-- SLIDE 49B BLOCK 26
namespace S49BB26

def onePlusOne : Nat := 1 + 1

example : (fun n : Nat => n + 1) 3 = 4 := by
  rfl

example : 2 + 3 = 5 := by
  rfl

example : onePlusOne = 2 := by
  rfl

-- Expected error:
-- example : 2 + 2 = 5 := by
--   rfl

end S49BB26
