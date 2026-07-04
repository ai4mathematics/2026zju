import Mathlib

/-!
# D3_04_Group_Instance

Standalone file extracted from `D3_Demo.lean` for classroom navigation.
-/

namespace LeanZjuD3.Ch04

/-!
## 4. Group instance: a two-element sign group

To build a `Group`, Lean needs operations and laws.  In this finite example the
laws are checked by case splitting.
-/

inductive Sign where
  | pos
  | neg
  deriving DecidableEq, Repr

open Sign

instance : Group Sign where
  mul a b :=
    match a, b with
    | pos, x => x
    | neg, pos => neg
    | neg, neg => pos
  one := pos
  inv a := a
  mul_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  one_mul := by
    intro a
    cases a <;> rfl
  mul_one := by
    intro a
    cases a <;> rfl
  inv_mul_cancel := by
    intro a
    cases a <;> rfl

#eval pos * neg
#eval neg * neg

#synth Group Sign
#check mul_assoc
#check one_mul
#check mul_one
#check inv_mul_cancel

example (a b c : Sign) : (a * b) * c = a * (b * c) := by
  exact mul_assoc a b c

example (a : Sign) : a⁻¹ * a = 1 := by
  exact inv_mul_cancel a

end LeanZjuD3.Ch04
