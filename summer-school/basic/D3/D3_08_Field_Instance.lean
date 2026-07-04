import Mathlib

/-!
# D3_08_Field_Instance

Standalone file extracted from `D3_Demo.lean` for classroom navigation.
-/

namespace LeanZjuD3.Ch08

/-!
## 8. Field instance: transport a field structure

A field is a commutative ring with nontriviality and inverses for nonzero
elements.  Here we wrap the rational numbers and transport the field structure.
-/

@[ext]
structure WrappedQ where
  val : Rat
  deriving DecidableEq, Repr

namespace WrappedQ

def equivRat : Equiv WrappedQ Rat where
  toFun x := x.val
  invFun q := { val := q }
  left_inv := by
    intro x
    ext
    rfl
  right_inv := by
    intro q
    rfl

instance : Field WrappedQ := equivRat.field

#synth Field WrappedQ
#check mul_inv_cancel₀
#check inv_zero
#check div_eq_mul_inv

#eval (({ val := 3 } : WrappedQ) + { val := 4 }).val
#eval (({ val := 3 } : WrappedQ) / { val := 2 }).val

example (x : WrappedQ) (hx : x ≠ 0) : x / x = 1 := by
  field_simp [hx]

end WrappedQ

end LeanZjuD3.Ch08
