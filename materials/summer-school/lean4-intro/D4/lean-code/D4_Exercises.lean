/-
  D4_Exercises.lean

  Exercises for D4: Analysis and Topology.
  This file requires a Lake project with Mathlib available.

  The exercises are intentionally small.  The goal is to practice reading
  Mathlib analysis statements and reusing API lemmas.
-/

import Mathlib

namespace D4Exercises

noncomputable section

open Filter
open MeasureTheory
open scoped Topology Interval

/-! ## Exercise 1: inspect the analysis API -/

#check ℝ
#check Field
#check LinearOrder
#check TopologicalSpace
#check MetricSpace
#check Filter
#check Tendsto
#check Continuous
#check ContinuousAt
#check deriv
#check HasDerivAt
#check intervalIntegral

/-!
Question:

For each item above, decide whether it is a structure, a function, or a
proposition-forming predicate.
-/

/-! ## Exercise 2: simple order and interval facts -/

example : (2 : ℝ) ≤ 5 := by
  sorry

example : (3 : ℝ) ∈ Set.Icc (1 : ℝ) 5 := by
  sorry

example (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) : 0 < x := by
  sorry

example (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) : x < 1 := by
  sorry

/-! ## Exercise 3: sequence and function limits -/

example (L : ℝ) :
    Tendsto (fun _ : ℕ => L) atTop (𝓝 L) := by
  sorry

example (a : ℝ) :
    Tendsto (fun x : ℝ => x) (𝓝 a) (𝓝 a) := by
  sorry

example (a c : ℝ) :
    Tendsto (fun x : ℝ => x + c) (𝓝 a) (𝓝 (a + c)) := by
  sorry

/-! ## Exercise 4: continuity -/

example : Continuous (fun x : ℝ => x) := by
  sorry

example (c : ℝ) : Continuous (fun _ : ℝ => c) := by
  sorry

example (c : ℝ) : Continuous (fun x : ℝ => x + c) := by
  sorry

example : Continuous (fun x : ℝ => x * x) := by
  sorry

/-! ## Exercise 5: derivatives -/

example (x : ℝ) :
    HasDerivAt (fun y : ℝ => y) 1 x := by
  sorry

example (c x : ℝ) :
    HasDerivAt (fun _ : ℝ => c) 0 x := by
  sorry

example (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
  sorry

example (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2 + y) (2 * x + 1) x := by
  sorry

/-! ## Exercise 6: interval integrals -/

example (a : ℝ) (f : ℝ → ℝ) :
    (∫ x in a..a, f x) = 0 := by
  sorry

example (a b : ℝ) :
    (∫ x in a..b, (0 : ℝ)) = 0 := by
  sorry

example (a b c : ℝ) :
    (∫ x in a..b, c) = (b - a) * c := by
  sorry

/-! ## Exercise 7: workflow target -/

/-!
Use `#check`, theorem search, and the examples above to try this target.
It may require a small simplification step after using the chain rule.

```lean
example (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y + 1) ^ 2) (2 * (x + 1)) x := by
  sorry
```
-/

end

end D4Exercises
