/-
  D4_AnalyticStructures.lean

  Mathlib demo file for Part I: Analytic Structures.
  This file requires a Lake project with Mathlib available.
-/

import Mathlib

namespace D4AnalyticStructures

/-! ## The real line as a structured object -/

#check ℝ
#check abs
#check Set.Icc
#check Set.Ioo

#synth Field ℝ
#synth LinearOrder ℝ
#synth TopologicalSpace ℝ
#synth MetricSpace ℝ

/-!
The point of these commands is not to memorize instance names.
The point is to see that `ℝ` carries algebraic, order, topological, and metric
structure simultaneously.
-/

/-! ## Order and intervals -/

example : (3 : ℝ) ≤ 5 := by
  norm_num

example : (3 : ℝ) ∈ Set.Icc (1 : ℝ) 5 := by
  constructor <;> norm_num

example (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) : 0 < x := by
  exact hx.1

example (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) : x < 1 := by
  exact hx.2

/-! ## Topology, metric spaces, and filters -/

#check TopologicalSpace
#check MetricSpace
#check Filter
#check nhds
#check atTop
#check Filter.Tendsto

open Filter
open scoped Topology

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

/-! ## Continuity as structure-aware API -/

#check Continuous
#check ContinuousAt
#check Continuous.tendsto

example : Continuous (fun x : ℝ => x) := by
  simpa using continuous_id

example (c : ℝ) : Continuous (fun _ : ℝ => c) := by
  simpa using continuous_const

/-!
The next file will focus on limits and continuity. This file only sets up the
map: order, topology, metric spaces, and filters are all part of the ambient
language of analysis in Mathlib.
-/

end D4AnalyticStructures
