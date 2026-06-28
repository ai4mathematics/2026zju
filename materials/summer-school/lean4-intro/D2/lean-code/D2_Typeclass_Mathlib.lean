/-
  D2_Typeclass_Mathlib.lean

  Mathlib-enhanced type class demo.

  This file requires a Lake project with mathlib available. It is not expected
  to compile in a bare Lean installation.
-/

import Mathlib

namespace D2TypeclassMathlib

/-! ## Familiar number systems and algebraic structures -/

#check ℕ
#check ℤ
#check ℚ
#check ℝ
#check ℂ

#synth Add ℕ
#synth Add ℤ
#synth Add ℚ
#synth Add ℂ

#synth Mul ℕ
#synth Mul ℤ
#synth Mul ℚ
#synth Mul ℂ

#synth CommSemiring ℕ
#synth Ring ℤ
#synth Field ℚ
#synth Field ℂ

/-!
The same notation is interpreted through different instances:
-/

#check ((1 : ℕ) + 2)
#check ((1 : ℤ) + 2)
#check ((1 : ℚ) + 2)
#check ((1 : ℂ) + 2)

/-! ## Generic algebraic statements -/

example {alpha : Type} [AddCommMonoid alpha] (a b : alpha) :
    a + b = b + a := by
  exact add_comm a b

example {alpha : Type} [Ring alpha] (a b c : alpha) :
    a * (b + c) = a * b + a * c := by
  exact left_distrib a b c

/-! ## A useful reading rule -/

/- 
When you see a theorem with a hypothesis such as `[Ring R]`, read it as:

  "For any type R, if Lean can find a ring structure on R, then ..."

This is why one theorem can apply to `ℤ`, `ℚ`, `ℝ`, `ℂ`, polynomial rings,
matrix rings, and many other mathematical objects.
-/

end D2TypeclassMathlib
