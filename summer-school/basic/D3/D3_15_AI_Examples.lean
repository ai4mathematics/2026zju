import Mathlib

/-! Requires a configured Mathlib Lake project; see `README.md` in this folder. -/

/-!
# D3_15_AI_Examples

Standalone file extracted from `D3_Demo.lean` for classroom navigation.
-/

namespace LeanZjuD3.Ch15

/-!
## 15. AI-assisted Lean: bad drafts and corrected code

The important classroom point is diagnostic: many AI errors are statement
errors, missing instance assumptions, or API hallucinations rather than just
tactic errors.
-/

section AIExamples

/-!
Bad draft: the statement is false at `x = 0`.

```lean
example (K : Type*) [Field K] (x : K) : x / x = 1 := by
  field_simp
```
-/

example (K : Type*) [Field K] (x : K) (hx : x ≠ 0) : x / x = 1 := by
  field_simp [hx]

/-!
Bad draft: the order of inverses is wrong in a noncommutative group.

```lean
example (G : Type*) [Group G] (a b : G) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  group
```
-/

example (G : Type*) [Group G] (a b : G) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  group

example (A : Type*) [CommGroup A] (a b : A) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  rw [mul_inv_rev]
  exact mul_comm b⁻¹ a⁻¹

/-!
Bad draft: a plausible theorem name that does not exist.

```lean
example : (Finset.range 5).card = 5 := by
  exact Finset.card_range_five
```
-/

#check Finset.card_range

example : (Finset.range 5).card = 5 := by
  exact Finset.card_range 5

/-!
Bad draft: `decide` is not arbitrary classical reasoning.

```lean
example (P : Prop) : P ∨ ¬ P := by
  decide
```
-/

example (P : Prop) [Decidable P] : P ∨ ¬ P := by
  by_cases h : P
  · exact Or.inl h
  · exact Or.inr h

example (P : Prop) : P ∨ ¬ P := by
  classical
  exact em P

/-!
Bad draft: the theorem is specialized to real numbers even though Mathlib has
a more reusable typeclass formulation.
-/

#check add_le_add_right

example {α : Type*} [Add α] [LE α] [AddLeftMono α]
    {a b : α} (h : a ≤ b) (c : α) :
    c + a ≤ c + b := by
  exact add_le_add_right h c

/-!
Successful AI drafts should still expose the algebraic structure and use a
small, checkable tactic step.
-/

example {R : Type*} [CommRing R] (a b c d : R)
    (h1 : c = d * a + b) (h2 : b = a * d) :
    c = 2 * a * d := by
  rw [h1, h2]
  ring

example (x y : ℝ) (h1 : x + y = 10) (h2 : x - y = 4) : x = 7 := by
  linarith

/-! Search tactics are useful during development; the comments show the
stable proof they discover. -/

example (n : Nat) : (Finset.range n).card = n := by
  exact?

example {G : Type*} [Group G] (a : G) : a⁻¹ * a = 1 := by
  apply?

example (n : Nat) : (Finset.range (n + 1)).card = n + 1 := by
  simp?

end AIExamples

end LeanZjuD3.Ch15
