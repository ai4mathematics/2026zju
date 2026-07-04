import Mathlib

/-!
# D3_05_Subgroup

Standalone file extracted from `D3_Demo.lean` for classroom navigation.
-/

namespace LeanZjuD3.Ch05

/-!
## 5. Subgroup: subtype plus group closure

A `Subgroup G` is a predicate on `G` together with proofs that it contains `1`
and is closed under multiplication and inverse.  Its elements are subtypes, so
`x.property` is the membership proof.
-/

section GroupSubstructures

def oneSubgroup (G : Type*) [Group G] : Subgroup G where
  carrier := {g | g = 1}
  one_mem' := by
    rfl
  mul_mem' := by
    intro a b ha hb
    rw [ha, hb]
    simp
  inv_mem' := by
    intro a ha
    rw [ha]
    simp

example (G : Type*) [Group G] : (1 : G) ∈ oneSubgroup G := by
  exact (oneSubgroup G).one_mem

example (G : Type*) [Group G] (x : oneSubgroup G) : (x : G) = 1 := by
  exact x.property

example (G : Type*) [Group G] : Group (oneSubgroup G) := by
  infer_instance

#check Subgroup
#check Subgroup.one_mem
#check Subgroup.mul_mem
#check Subgroup.inv_mem

end GroupSubstructures

end LeanZjuD3.Ch05
