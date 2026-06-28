/-
  D4_LimitsContinuity.lean

  Mathlib demo file for Part II: Limits and Continuity.
  This file requires a Lake project with Mathlib available.
-/

import Mathlib

namespace D4LimitsContinuity

open Filter
open scoped Topology

/-! ## Reading filter statements -/

#check Filter.Tendsto
#check atTop
#check nhds
#check nhdsWithin

/-!
Sequence limit:

  ε-N language:
    for every ε > 0, eventually |u n - L| < ε

  filter language:
    `Tendsto u atTop (𝓝 L)`
-/

example (L : ℝ) : Tendsto (fun _ : ℕ => L) atTop (𝓝 L) := by
  simpa using tendsto_const_nhds

/-!
Function limit:

  ε-δ language:
    for every ε > 0, if x is sufficiently close to a, then f x is close to L

  filter language:
    `Tendsto f (𝓝 a) (𝓝 L)`
-/

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

/-! ## Punctured neighborhoods -/

/-!
For a punctured limit at `a`, Mathlib often uses `𝓝[≠] a`.
This corresponds to the condition `x ≠ a`, or in metric language,
`0 < |x - a|`.
-/

#check nhdsWithin
#check Filter.Tendsto

/- 
Possible live goal after checking lemma names in the local Mathlib version:

  example (a : ℝ) : Tendsto (fun x : ℝ => x) (𝓝[≠] a) (𝓝 a) := by
    ...

The important point for this lecture is the reading of `𝓝[≠] a` as a
punctured neighborhood filter.
-/

/-! ## Continuity -/

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

/-! ## A small comparison table in Lean comments -/

/- 
Traditional statement              Filter statement
---------------------------------------------------------------
u_n -> L                           Tendsto u atTop (𝓝 L)
x -> a, f x -> L                   Tendsto f (𝓝 a) (𝓝 L)
x -> a, x ≠ a, f x -> L            Tendsto f (𝓝[≠] a) (𝓝 L)
f continuous at a                  Tendsto f (𝓝 a) (𝓝 (f a))

In practice, Mathlib proofs usually combine `Tendsto` and `Continuous` lemmas
rather than unfolding epsilon-delta definitions.
-/

end D4LimitsContinuity
