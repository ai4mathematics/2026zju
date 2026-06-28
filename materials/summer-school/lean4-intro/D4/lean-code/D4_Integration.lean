/-
  D4_Integration.lean

  Mathlib demo file for Part IV: Integration.
  This file requires a Lake project with Mathlib available.
-/

import Mathlib

namespace D4Integration

noncomputable section

open MeasureTheory
open scoped Topology Interval

/-! ## Interval integral API -/

#check intervalIntegral
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

/-! ## Constant functions -/

example (a b c : ℝ) :
    (∫ x in a..b, c) = (b - a) * c := by
  simpa using (intervalIntegral.integral_const (a := a) (b := b) (c := c))

example (a b : ℝ) :
    (∫ x in a..b, (0 : ℝ)) = 0 := by
  simp

example (a : ℝ) (f : ℝ → ℝ) :
    (∫ x in a..a, f x) = 0 := by
  simp

/-! ## Linearity map -/

#check intervalIntegral.integral_add
#check intervalIntegral.integral_sub
#check intervalIntegral.integral_const_mul
#check intervalIntegral.integral_mul_const

/-!
For classroom purposes, it is usually enough to know that interval integrals
are linear under the usual integrability assumptions. The exact assumptions are
part of the API and can be inspected with `#check`.
-/

/-! ## Fundamental theorem of calculus: map of theorem names -/

#check intervalIntegral.integral_hasDerivAt_right
#check intervalIntegral.deriv_integral_right
#check intervalIntegral.integral_hasDerivAt_left
#check intervalIntegral.integral_eq_sub_of_hasDerivAt
#check intervalIntegral.integral_deriv_eq_sub
#check intervalIntegral.integral_deriv_eq_sub'

/-!
Informal shape of FTC-1:

  If `f` is continuous, then

    F x = ∫ t in a..x, f t

  has derivative `f x`.

Informal shape of FTC-2:

  If `F' = f`, then

    ∫ x in a..b, f x = F b - F a.

In Mathlib, these statements come with precise continuity, integrability, and
one-sided derivative assumptions. The theorem names above are entry points for
search and live proof repair.
-/

/-! ## A deliberately search-oriented target -/

/- 
Possible live target:

  example (a b c : ℝ) :
      (∫ x in a..b, c) = (b - a) * c := by
    simpa using (intervalIntegral.integral_const (a := a) (b := b) (c := c))

More ambitious targets, such as computing `∫ x in a..b, x`, should be chosen
after checking the local Mathlib theorem names. This is a good place to model
the workflow:

  1. write the mathematical target;
  2. search for an interval-integral theorem;
  3. inspect the exact statement with `#check`;
  4. adapt the target or assumptions.
-/

end

end D4Integration
