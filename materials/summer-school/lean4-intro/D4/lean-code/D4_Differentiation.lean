/-
  D4_Differentiation.lean

  Mathlib demo file for Part III: Differentiation.
  This file requires a Lake project with Mathlib available.
-/

import Mathlib

namespace D4Differentiation

noncomputable section

/-! ## The two common interfaces -/

#check deriv
#check HasDerivAt

/-!
Reading guide:

* `deriv f x` is the derivative as a value.
* `HasDerivAt f f' x` is a proposition: `f` has derivative `f'` at `x`.

Many calculus rules are easiest to use through `HasDerivAt`.
-/

/-! ## Basic derivative facts -/

#check hasDerivAt_id
#check hasDerivAt_const
#check HasDerivAt.add
#check HasDerivAt.mul
#check HasDerivAt.comp

example (x : ℝ) : HasDerivAt (fun y : ℝ => y) 1 x := by
  simpa using (hasDerivAt_id x)

example (c x : ℝ) : HasDerivAt (fun _ : ℝ => c) 0 x := by
  simpa using (hasDerivAt_const (x := x) (c := c))

/-! ## Powers -/

#check hasDerivAt_pow
#check deriv_pow

example (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
  simpa using (hasDerivAt_pow 2 x)

example (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
  simpa using (hasDerivAt_pow 3 x)

/-! ## Combining rules -/

example (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 3 + y) (3 * x ^ 2 + 1) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    simpa using (hasDerivAt_pow 3 x)
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := by
    simpa using (hasDerivAt_id x)
  simpa using hpow.add hid

/-! ## The simplifier can compute many simple derivatives -/

example (x : ℝ) : deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
  simp

example (x : ℝ) : deriv (fun y : ℝ => y ^ 3 + y) x = 3 * x ^ 2 + 1 := by
  simp

/-! ## Chain-rule target -/

/- 
Possible live example after checking local theorem names:

  example (x : ℝ) :
      HasDerivAt (fun y : ℝ => (y + 1) ^ 2) (2 * (x + 1)) x := by
    ...

The intended proof combines:

  * derivative of `fun y => y + 1`;
  * derivative of `fun z => z ^ 2`;
  * `HasDerivAt.comp`.
-/

end

end D4Differentiation
