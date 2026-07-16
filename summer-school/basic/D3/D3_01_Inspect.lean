import Mathlib

/-! Requires a configured Mathlib Lake project; see `README.md` in this folder. -/

/-!
# D3_01_Inspect

Standalone file extracted from `D3_Demo.lean` for classroom navigation.
-/

namespace LeanZjuD3.Ch01

/-!
## 1. Inspect first

The first classroom habit is to ask Lean what structure, notation, and theorem
names already mean.
-/

#check Group
#check AddGroup
#check AddCommGroup
#check Ring
#check Field
#check Module
#check CategoryTheory.Category
#check Subtype
#check Subgroup
#check Subring
#check Submodule
#check Fact
#check inferInstance

example (a b : ℝ) (h : a ≤ b) : 0 ≤ b - a := by
  linarith

example : (2 : Nat) + 2 = 4 := by
  decide

example (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

end LeanZjuD3.Ch01
