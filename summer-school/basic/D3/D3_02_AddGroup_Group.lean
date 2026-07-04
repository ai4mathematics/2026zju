import Mathlib

/-!
# D3_02_AddGroup_Group

Standalone file extracted from `D3_Demo.lean` for classroom navigation.
-/

namespace LeanZjuD3.Ch02

/-!
## 2. AddGroup versus Group

`AddGroup` and `Group` express the same algebraic pattern with different
notation.  `AddGroup A` uses `0`, `+`, and unary minus; `Group G` uses `1`,
`*`, and inverse.  Many additive facts are generated from multiplicative ones
by Mathlib's `to_additive` machinery, but in everyday proofs the notations tell
Lean which typeclass to search for.
-/

section AddGroupVsGroup

#check AddGroup
#check Group
#check neg_add_cancel
#check inv_mul_cancel

example (A : Type*) [AddGroup A] (a : A) : -a + a = 0 := by
  exact neg_add_cancel a

example (G : Type*) [Group G] (g : G) : g⁻¹ * g = 1 := by
  exact inv_mul_cancel g

example (A : Type*) [AddGroup A] (a b c : A) :
    (a + b) + c = a + (b + c) := by
  exact add_assoc a b c

example (G : Type*) [Group G] (a b c : G) :
    (a * b) * c = a * (b * c) := by
  exact mul_assoc a b c

#synth AddGroup ℤ

example (a : ℤ) : -a + a = 0 := by
  exact neg_add_cancel a

end AddGroupVsGroup

end LeanZjuD3.Ch02
