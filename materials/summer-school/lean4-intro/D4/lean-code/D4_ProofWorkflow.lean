/-
  D4_ProofWorkflow.lean

  Mathlib demo file for the final workflow segment.
  This file requires a Lake project with Mathlib available.

  The point of this file is not to introduce many new analysis facts.
  It is a guided script for turning a mathematical target into a Lean proof:

  1. inspect the goal;
  2. inspect API statements with `#check`;
  3. try small reusable lemmas;
  4. let `simp`, `simpa`, and theorem search do the boring work;
  5. keep an ambitious target as a search exercise.
-/

import Mathlib

namespace D4ProofWorkflow

noncomputable section

open Filter
open MeasureTheory
open scoped Topology Interval

/-! ## 1. Start by reading the objects -/

#check ℝ
#check TopologicalSpace
#check MetricSpace
#check Filter
#check Tendsto
#check Continuous
#check deriv
#check HasDerivAt
#check intervalIntegral

/-!
In class, pause here and ask:

* What is the domain?
* What is the codomain?
* Is the statement about a value, or about a proposition?
* Which structure is being used: order, topology, metric, algebra, measure?
-/

/-! ## 2. A small target: continuity -/

#check continuous_id
#check continuous_const
#check Continuous.add
#check Continuous.mul

example (c : ℝ) : Continuous (fun x : ℝ => x + c) := by
  simpa using (continuous_id.add continuous_const)

example : Continuous (fun x : ℝ => x * x) := by
  simpa using (continuous_id.mul continuous_id)

/-!
Workflow note:

The mathematical proof says "identity and constant functions are continuous,
and sums/products of continuous functions are continuous."  The Lean proof is
almost the same sentence, but written with API lemmas.
-/

/-! ## 3. A small target: limit from continuity -/

#check Continuous.tendsto
#check tendsto_id
#check tendsto_const_nhds

example (a c : ℝ) :
    Tendsto (fun x : ℝ => x + c) (𝓝 a) (𝓝 (a + c)) := by
  simpa using (continuous_id.add continuous_const).tendsto a

example (a : ℝ) :
    Tendsto (fun x : ℝ => x * x) (𝓝 a) (𝓝 (a * a)) := by
  simpa using (continuous_id.mul continuous_id).tendsto a

/-!
This is the bridge from Part II:

  continuity at `a`
  -> a `Tendsto` statement at `𝓝 a`.
-/

/-! ## 4. A small target: derivative -/

#check hasDerivAt_id
#check hasDerivAt_const
#check hasDerivAt_pow
#check HasDerivAt.add

example (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2 + y) (2 * x + 1) x := by
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x)
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := by
    simpa using (hasDerivAt_id x)
  simpa using hsq.add hid

/-!
This is a good place to demonstrate proof repair:

* if `simpa` fails, inspect the exact derivative expression;
* compare `2 * x + 1` with what Mathlib produced;
* try `ring_nf` or rewrite the target if the expressions are algebraically
  equal but syntactically different.
-/

/-! ## 5. A small target: interval integral -/

#check intervalIntegral.integral_same
#check intervalIntegral.integral_const

example (a : ℝ) (f : ℝ → ℝ) :
    (∫ x in a..a, f x) = 0 := by
  simp

example (a b c : ℝ) :
    (∫ x in a..b, c) = (b - a) * c := by
  simpa using (intervalIntegral.integral_const (a := a) (b := b) (c := c))

/-! ## 6. A deliberately search-oriented target -/

/-!
Classroom exercise:

Try to prove a derivative statement for the composition

  x ↦ (x + 1)^2.

The intended mathematical proof is:

1. `x ↦ x + 1` has derivative `1`;
2. `z ↦ z^2` has derivative `2*z`;
3. compose the two derivative facts;
4. simplify the resulting expression.

Possible starting point:

```lean
example (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y + 1) ^ 2) (2 * (x + 1)) x := by
  -- search with:
  -- #check HasDerivAt.comp
  -- #check HasDerivAt.add
  -- #check hasDerivAt_pow
  -- #check hasDerivAt_id
  sorry
```

This target is intentionally left as a live search problem.  It is useful for
showing that a proof can be mathematically obvious but still require API
navigation in Lean.
-/

/-! ## 7. A compact workflow checklist -/

/-!
When a Mathlib analysis proof gets stuck:

1. Read the goal and local hypotheses.
2. `#check` the main definitions in the goal.
3. Search for the theorem whose conclusion resembles the goal.
4. Prefer API lemmas over unfolding definitions.
5. Use `simp` or `simpa` for small normalization.
6. If theorem names or assumptions are wrong, repair from Lean's error message.
7. Treat AI output as a draft; treat Lean as the verifier.
-/

end

end D4ProofWorkflow
