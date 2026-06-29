/-
  D4_All.lean

  Classroom file for D4: Analysis and Topology.

  This file keeps a single `import Mathlib` and then collects the classroom
  demos from the separate D4 files.  Use this file during the lecture to avoid
  repeatedly loading Mathlib from several files.

  Navigation:

  * Ctrl+F `D4-IDX`   top index
  * Ctrl+F `D4-P1`    Analytic Structures
  * Ctrl+F `D4-P2`    Limits and Continuity
  * Ctrl+F `D4-P2E`   Epsilon/filter comparison
  * Ctrl+F `D4-P3`    Differentiation
  * Ctrl+F `D4-P4`    Integration
  * Ctrl+F `D4-WF`    Proof Workflow
  * Ctrl+F `D4-EX`    Exercises
  * Ctrl+F `D4-SOL`   Selected Solutions

  The separate source files are still kept in `codeD4/`.
-/

import Mathlib

namespace D4All

noncomputable section

open Filter
open MeasureTheory
open scoped Topology Interval

/-!
# D4-IDX: Index

Suggested classroom order:

1. `D4-P1`: analytic structures around `ℝ`.
2. `D4-P2`: filter language for limits and continuity.
3. `D4-P2E`: comments comparing epsilon language and filters.
4. `D4-P3`: `deriv` and `HasDerivAt`.
5. `D4-P4`: interval integrals and FTC map.
6. `D4-WF`: proof workflow and live repair target.
7. `D4-EX`: exercises for students.
8. `D4-SOL`: selected solutions for reference.
-/

/-! # D4-P1: Analytic Structures -/

namespace Part1AnalyticStructures

/-! ## D4-P1.1: The real line as a structured object -/

#check ℝ
#check abs
#check Set.Icc
#check Set.Ioo

-- The class name does not exist in this Mathlib version.
-- Try this live to see an "unknown identifier" error:
-- #synth LinearOrderedField ℝ

-- The class exists, but there is no such instance.
-- Try this live to see a "failed to synthesize" error:
-- #synth Field Nat


-- These instances do exist.
#synth Field ℝ
#synth LinearOrder ℝ
#synth TopologicalSpace ℝ
#synth MetricSpace ℝ

/-!
The point of these commands is not to memorize instance names.
The point is to see that `ℝ` carries algebraic, order, topological, and metric
structure simultaneously.
-/

/-! ## D4-P1.2: Order and intervals -/

example : (3 : ℝ) ≤ 5 := by
  norm_num

example : (3 : ℝ) ∈ Set.Icc (1 : ℝ) 5 := by
  constructor <;> norm_num

example (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) : 0 < x := by
  exact hx.1

example (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) : x < 1 := by
  exact hx.2

/-! ## D4-P1.3: Topology, metric spaces, and filters -/

#check TopologicalSpace
#check MetricSpace
#check Filter
#check nhds
#check atTop
#check Filter.Tendsto

/-!
Read:

  `Tendsto f l₁ l₂`

as:

  if the input follows the filter `l₁`,
  then the output follows the filter `l₂`.
-/

example (a : ℝ) : Tendsto (fun x : ℝ => x) (𝓝 a) (𝓝 a) := by
  simpa using tendsto_id

example (c : ℝ) : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := by
  simpa using tendsto_const_nhds

/-! ## D4-P1.4: Continuity as structure-aware API -/

#check Continuous
#check ContinuousAt
#check Continuous.tendsto

example : Continuous (fun x : ℝ => x) := by
  simpa using continuous_id

example (c : ℝ) : Continuous (fun _ : ℝ => c) := by
  simpa using continuous_const

end Part1AnalyticStructures

/-! # D4-P2: Limits and Continuity -/

namespace Part2LimitsContinuity

/-! ## D4-P2.1: Reading filter statements -/

#check Filter.Tendsto
#check atTop
#check nhds
#check nhdsWithin

example (L : ℝ) : Tendsto (fun _ : ℕ => L) atTop (𝓝 L) := by
  simpa using tendsto_const_nhds

example (a : ℝ) : Tendsto (fun x : ℝ => x) (𝓝 a) (𝓝 a) := by
  simpa using tendsto_id

example (a c : ℝ) :
    Tendsto (fun x : ℝ => x + c) (𝓝 a) (𝓝 (a + c)) := by
  have hx : Tendsto (fun x : ℝ => x) (𝓝 a) (𝓝 a) := by
    simpa using tendsto_id
  have hc : Tendsto (fun _ : ℝ => c) (𝓝 a) (𝓝 c) := by
    simpa using tendsto_const_nhds
  simpa using hx.add hc

example (a c : ℝ) :
    Tendsto (fun x : ℝ => c + x) (𝓝 a) (𝓝 (c + a)) := by
  have hc : Tendsto (fun _ : ℝ => c) (𝓝 a) (𝓝 c) := by
    simpa using tendsto_const_nhds
  have hx : Tendsto (fun x : ℝ => x) (𝓝 a) (𝓝 a) := by
    simpa using tendsto_id
  simpa using hc.add hx

/-! ## D4-P2E: Epsilon/filter comparison -/

/-!
Sequence limit:

  epsilon-N language:
    for every epsilon > 0, eventually `|u n - L| < epsilon`

  filter language:
    `Tendsto u atTop (𝓝 L)`

Function limit:

  epsilon-delta language:
    for every epsilon > 0, if `x` is sufficiently close to `a`,
    then `f x` is close to `L`

  filter language:
    `Tendsto f (𝓝 a) (𝓝 L)`

Punctured limit:

  metric language:
    `0 < |x - a|` and `|x - a| < delta`

  filter language:
    `Tendsto f (𝓝[≠] a) (𝓝 L)`
-/

/-!
Possible live goal after checking lemma names in the local Mathlib version:

```lean
example (a : ℝ) : Tendsto (fun x : ℝ => x) (𝓝[≠] a) (𝓝 a) := by
  ...
```

The important classroom point is the reading of `𝓝[≠] a` as a punctured
neighborhood filter.
-/

/-! ## D4-P2.2: Continuity -/

#check Continuous
#check ContinuousAt
#check Continuous.tendsto
#check Continuous.add
#check Continuous.mul

example : Continuous (fun x : ℝ => x) := by
  simpa using continuous_id

example (c : ℝ) : Continuous (fun _ : ℝ => c) := by
  simpa using continuous_const

example (c : ℝ) : Continuous (fun x : ℝ => x + c) := by
  simpa using (continuous_id.add continuous_const)

example : Continuous (fun x : ℝ => x * x) := by
  simpa using (continuous_id.mul continuous_id)

example (a : ℝ) :
    Tendsto (fun x : ℝ => x * x) (𝓝 a) (𝓝 (a * a)) := by
  exact (continuous_id.mul continuous_id).tendsto a

/-!
Traditional statement              Filter statement
---------------------------------------------------------------
u_n -> L                           Tendsto u atTop (𝓝 L)
x -> a, f x -> L                   Tendsto f (𝓝 a) (𝓝 L)
x -> a, x ≠ a, f x -> L            Tendsto f (𝓝[≠] a) (𝓝 L)
f continuous at a                  Tendsto f (𝓝 a) (𝓝 (f a))

In practice, Mathlib proofs usually combine `Tendsto` and `Continuous` lemmas
rather than unfolding epsilon-delta definitions.
-/

end Part2LimitsContinuity

/-! # D4-P3: Differentiation -/

namespace Part3Differentiation

/-! ## D4-P3.1: The two common interfaces -/

#check deriv
#check HasDerivAt

/-!
Reading guide:

* `deriv f x` is the derivative as a value.
* `HasDerivAt f f' x` is a proposition: `f` has derivative `f'` at `x`.

Many calculus rules are easiest to use through `HasDerivAt`.
-/

/-! ## D4-P3.2: Basic derivative facts -/

#check hasDerivAt_id
#check hasDerivAt_const
#check HasDerivAt.add
#check HasDerivAt.mul
#check HasDerivAt.comp

example (x : ℝ) : HasDerivAt (fun y : ℝ => y) 1 x := by
  simpa using (hasDerivAt_id x)

example (c x : ℝ) : HasDerivAt (fun _ : ℝ => c) 0 x := by
  simpa using (hasDerivAt_const (x := x) (c := c))

/-! ## D4-P3.3: Powers -/

#check hasDerivAt_pow
#check deriv_pow

example (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
  simpa using (hasDerivAt_pow 2 x)

example (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
  simpa using (hasDerivAt_pow 3 x)

/-! ## D4-P3.4: Combining rules -/

example (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 3 + y) (3 * x ^ 2 + 1) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    simpa using (hasDerivAt_pow 3 x)
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := by
    simpa using (hasDerivAt_id x)
  simpa using hpow.add hid

/-! ## D4-P3.5: The simplifier can compute many simple derivatives -/

example (x : ℝ) : deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
  simp

example (x : ℝ) : deriv (fun y : ℝ => y ^ 3 + y) x = 3 * x ^ 2 + 1 := by
  simp

/-! ## D4-P3.6: Chain-rule live target -/

/-!
Possible live example after checking local theorem names:

```lean
example (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y + 1) ^ 2) (2 * (x + 1)) x := by
  ...
```

The intended proof combines:

* derivative of `fun y => y + 1`;
* derivative of `fun z => z ^ 2`;
* `HasDerivAt.comp`.
-/

end Part3Differentiation

/-! # D4-P4: Integration -/

namespace Part4Integration

/-! ## D4-P4.1: Interval integral API -/

#check IntervalIntegrable
#check intervalIntegral.integral_same
#check intervalIntegral.integral_symm
#check intervalIntegral.integral_const
#check intervalIntegral.integral_add

/-!
The notation

  `∫ x in a..b, f x`

is the interval integral over the oriented interval from `a` to `b`.
It is built on measure-theoretic integration, but in this lecture we mostly
treat it as an API for ordinary one-variable calculus.
-/

/-! ## D4-P4.2: Constant functions -/

example (a b c : ℝ) :
    (∫ x in a..b, c) = (b - a) * c := by
  simpa using (intervalIntegral.integral_const (a := a) (b := b) (c := c))

example (a b : ℝ) :
    (∫ x in a..b, (0 : ℝ)) = 0 := by
  simp

example (a : ℝ) (f : ℝ → ℝ) :
    (∫ x in a..a, f x) = 0 := by
  simp

/-! ## D4-P4.3: Linearity map -/

#check intervalIntegral.integral_add
#check intervalIntegral.integral_sub
#check intervalIntegral.integral_const_mul
#check intervalIntegral.integral_mul_const

/-!
For classroom purposes, it is usually enough to know that interval integrals
are linear under the usual integrability assumptions. The exact assumptions are
part of the API and can be inspected with `#check`.
-/

/-! ## D4-P4.4: Fundamental theorem of calculus map -/

/-!
Informal shape of FTC-1:

  If `f` is continuous, then

    F x = ∫ t in a..x, f t

  has derivative `f x`.

Informal shape of FTC-2:

  If `F' = f`, then

    ∫ x in a..b, f x = F b - F a.

The theorem names around FTC are version-sensitive.  During lecture, search in
the local Mathlib docs for names such as:

* `intervalIntegral.integral_hasDerivAt_right`
* `intervalIntegral.deriv_integral_right`
* `intervalIntegral.integral_eq_sub_of_hasDerivAt`
* `intervalIntegral.integral_deriv_eq_sub`
-/

/-! ## D4-P4.5: Search-oriented target -/

/-!
More ambitious targets, such as computing `∫ x in a..b, x`, should be chosen
after checking the local Mathlib theorem names. This is a good place to model
the workflow:

1. write the mathematical target;
2. search for an interval-integral theorem;
3. inspect the exact statement with `#check`;
4. adapt the target or assumptions.
-/

end Part4Integration

/-! # D4-WF: Proof Workflow -/

namespace ProofWorkflow

/-! ## D4-WF.1: Start by reading the objects -/

#check ℝ
#check TopologicalSpace
#check MetricSpace
#check Filter
#check Tendsto
#check Continuous
#check deriv
#check HasDerivAt
#check IntervalIntegrable

/-!
In class, pause here and ask:

* What is the domain?
* What is the codomain?
* Is the statement about a value, or about a proposition?
* Which structure is being used: order, topology, metric, algebra, measure?
-/

/-! ## D4-WF.2: A small target: continuity -/

#check continuous_id
#check continuous_const
#check Continuous.add
#check Continuous.mul

example (c : ℝ) : Continuous (fun x : ℝ => x + c) := by
  simpa using (continuous_id.add continuous_const)

example : Continuous (fun x : ℝ => x * x) := by
  simpa using (continuous_id.mul continuous_id)

/-!
The mathematical proof says "identity and constant functions are continuous,
and sums/products of continuous functions are continuous." The Lean proof is
almost the same sentence, but written with API lemmas.
-/

/-! ## D4-WF.3: A small target: limit from continuity -/

#check Continuous.tendsto
#check tendsto_id
#check tendsto_const_nhds

example (a c : ℝ) :
    Tendsto (fun x : ℝ => x + c) (𝓝 a) (𝓝 (a + c)) := by
  simpa using (continuous_id.add continuous_const).tendsto a

example (a : ℝ) :
    Tendsto (fun x : ℝ => x * x) (𝓝 a) (𝓝 (a * a)) := by
  simpa using (continuous_id.mul continuous_id).tendsto a

/-! ## D4-WF.4: A small target: derivative -/

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

/-! ## D4-WF.5: A small target: interval integral -/

#check intervalIntegral.integral_same
#check intervalIntegral.integral_const

example (a : ℝ) (f : ℝ → ℝ) :
    (∫ x in a..a, f x) = 0 := by
  simp

example (a b c : ℝ) :
    (∫ x in a..b, c) = (b - a) * c := by
  simpa using (intervalIntegral.integral_const (a := a) (b := b) (c := c))

/-! ## D4-WF.6: A deliberately search-oriented target -/

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
-/

/-! ## D4-WF.7: Compact workflow checklist -/

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

end ProofWorkflow

/-! # D4-EX: Exercises -/

namespace Exercises

/-! ## D4-EX.1: Inspect the analysis API -/

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
#check IntervalIntegrable

/-!
Question:

For each item above, decide whether it is a structure, a function, or a
proposition-forming predicate.
-/

/-! ## D4-EX.2: Simple order and interval facts -/

example : (2 : ℝ) ≤ 5 := by
  sorry

example : (3 : ℝ) ∈ Set.Icc (1 : ℝ) 5 := by
  sorry

example (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) : 0 < x := by
  sorry

example (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) : x < 1 := by
  sorry

/-! ## D4-EX.3: Sequence and function limits -/

example (L : ℝ) :
    Tendsto (fun _ : ℕ => L) atTop (𝓝 L) := by
  sorry

example (a : ℝ) :
    Tendsto (fun x : ℝ => x) (𝓝 a) (𝓝 a) := by
  sorry

example (a c : ℝ) :
    Tendsto (fun x : ℝ => x + c) (𝓝 a) (𝓝 (a + c)) := by
  sorry

/-! ## D4-EX.4: Continuity -/

example : Continuous (fun x : ℝ => x) := by
  sorry

example (c : ℝ) : Continuous (fun _ : ℝ => c) := by
  sorry

example (c : ℝ) : Continuous (fun x : ℝ => x + c) := by
  sorry

example : Continuous (fun x : ℝ => x * x) := by
  sorry

/-! ## D4-EX.5: Derivatives -/

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

/-! ## D4-EX.6: Interval integrals -/

example (a : ℝ) (f : ℝ → ℝ) :
    (∫ x in a..a, f x) = 0 := by
  sorry

example (a b : ℝ) :
    (∫ x in a..b, (0 : ℝ)) = 0 := by
  sorry

example (a b c : ℝ) :
    (∫ x in a..b, c) = (b - a) * c := by
  sorry

end Exercises

/-! # D4-SOL: Selected Solutions -/

namespace SelectedSolutions

/-! ## D4-SOL.1: Order and interval facts -/

example : (2 : ℝ) ≤ 5 := by
  norm_num

example : (3 : ℝ) ∈ Set.Icc (1 : ℝ) 5 := by
  constructor <;> norm_num

example (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) : 0 < x := by
  exact hx.1

example (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) : x < 1 := by
  exact hx.2

/-! ## D4-SOL.2: Sequence and function limits -/

example (L : ℝ) :
    Tendsto (fun _ : ℕ => L) atTop (𝓝 L) := by
  simpa using tendsto_const_nhds

example (a : ℝ) :
    Tendsto (fun x : ℝ => x) (𝓝 a) (𝓝 a) := by
  simpa using tendsto_id

example (a c : ℝ) :
    Tendsto (fun x : ℝ => x + c) (𝓝 a) (𝓝 (a + c)) := by
  have hx : Tendsto (fun x : ℝ => x) (𝓝 a) (𝓝 a) := by
    simpa using tendsto_id
  have hc : Tendsto (fun _ : ℝ => c) (𝓝 a) (𝓝 c) := by
    simpa using tendsto_const_nhds
  simpa using hx.add hc

/-! ## D4-SOL.3: Continuity -/

example : Continuous (fun x : ℝ => x) := by
  simpa using continuous_id

example (c : ℝ) : Continuous (fun _ : ℝ => c) := by
  simpa using continuous_const

example (c : ℝ) : Continuous (fun x : ℝ => x + c) := by
  simpa using (continuous_id.add continuous_const)

example : Continuous (fun x : ℝ => x * x) := by
  simpa using (continuous_id.mul continuous_id)

/-! ## D4-SOL.4: Derivatives -/

example (x : ℝ) :
    HasDerivAt (fun y : ℝ => y) 1 x := by
  simpa using (hasDerivAt_id x)

example (c x : ℝ) :
    HasDerivAt (fun _ : ℝ => c) 0 x := by
  simpa using (hasDerivAt_const (x := x) (c := c))

example (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
  simpa using (hasDerivAt_pow 2 x)

example (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2 + y) (2 * x + 1) x := by
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x)
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := by
    simpa using (hasDerivAt_id x)
  simpa using hsq.add hid

/-! ## D4-SOL.5: Interval integrals -/

example (a : ℝ) (f : ℝ → ℝ) :
    (∫ x in a..a, f x) = 0 := by
  simp

example (a b : ℝ) :
    (∫ x in a..b, (0 : ℝ)) = 0 := by
  simp

example (a b c : ℝ) :
    (∫ x in a..b, c) = (b - a) * c := by
  simpa using (intervalIntegral.integral_const (a := a) (b := b) (c := c))

/-! ## D4-SOL.6: Chain-rule target, kept as live repair material -/

/-!
One possible proof shape, after checking the local chain-rule theorem names:

```lean
example (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y + 1) ^ 2) (2 * (x + 1)) x := by
  have hinner : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
    simpa using
      (hasDerivAt_id x).add (hasDerivAt_const (x := x) (c := (1 : ℝ)))
  have houter : HasDerivAt (fun z : ℝ => z ^ 2) (2 * (x + 1)) (x + 1) := by
    simpa using (hasDerivAt_pow 2 (x + 1))
  simpa using houter.comp x hinner
```

Depending on the Mathlib version, the final line may need a small rewrite or
`ring_nf`.  This is intentionally kept as live repair material.
-/

end SelectedSolutions

end

end D4All
