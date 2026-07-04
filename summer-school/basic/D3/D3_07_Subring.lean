import Mathlib

/-!
# D3_07_Subring

Standalone file extracted from `D3_Demo.lean` for classroom navigation.
-/

namespace LeanZjuD3.Ch07

/-!
## 7. Subring: subtype plus ring closure

A `Subring R` stores a carrier predicate and closure proofs for `0`, `1`,
addition, negation, and multiplication.  Once built, Mathlib supplies the ring
structure on the subtype.
-/

section RingSubstructures

def diagonalSubring : Subring (ℤ × ℤ) where
  carrier := {p | p.1 = p.2}
  zero_mem' := by
    simp
  one_mem' := by
    simp
  add_mem' := by
    intro a b ha hb
    simp at ha hb ⊢
    rw [ha, hb]
  neg_mem' := by
    intro a ha
    simp at ha ⊢
    rw [ha]
  mul_mem' := by
    intro a b ha hb
    simp at ha hb ⊢
    rw [ha, hb]

example : ((3, 3) : ℤ × ℤ) ∈ diagonalSubring := by
  norm_num [diagonalSubring]

example (x : diagonalSubring) : (x : ℤ × ℤ).1 = (x : ℤ × ℤ).2 := by
  exact x.property

example : Ring diagonalSubring := by
  infer_instance

#check Subring
#check Subring.zero_mem
#check Subring.one_mem
#check Subring.add_mem
#check Subring.neg_mem
#check Subring.mul_mem

end RingSubstructures

end LeanZjuD3.Ch07
