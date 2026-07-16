import Mathlib

/-! Requires a configured Mathlib Lake project; see `README.md` in this folder. -/

/-!
# D3_09_Module_Submodule

Standalone file extracted from `D3_Demo.lean` for classroom navigation.
-/

namespace LeanZjuD3.Ch09

/-!
## 9. Module: scalar multiplication compatible with addition

Before speaking about vector spaces, Lean asks for the additive group of
vectors and a scalar action satisfying the usual module laws.  A vector space is
just a module over a field.
-/

section ModuleBasics

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

#check Module
#check smul_add
#check add_smul
#check one_smul
#check mul_smul

example (a : K) (u v : V) : a • (u + v) = a • u + a • v := by
  exact smul_add a u v

example (a b : K) (v : V) : (a + b) • v = a • v + b • v := by
  exact add_smul a b v

example (a b : K) (v : V) : (a * b) • v = a • (b • v) := by
  exact mul_smul a b v

example : Module ℚ ℚ := by
  infer_instance

example : Module ℚ (ℚ × ℚ) := by
  infer_instance

def diagonalSubmodule : Submodule ℚ (ℚ × ℚ) where
  carrier := {p | p.1 = p.2}
  zero_mem' := by
    simp
  add_mem' := by
    intro a b ha hb
    simp at ha hb ⊢
    rw [ha, hb]
  smul_mem' := by
    intro c p hp
    change (c * p.1 = c * p.2)
    rw [hp]

example : ((2, 2) : ℚ × ℚ) ∈ diagonalSubmodule := by
  norm_num [diagonalSubmodule]

example (x : diagonalSubmodule) : (x : ℚ × ℚ).1 = (x : ℚ × ℚ).2 := by
  exact x.property

example : Module ℚ diagonalSubmodule := by
  infer_instance

#check Submodule
#check Submodule.add_mem
#check Submodule.smul_mem

end ModuleBasics

end LeanZjuD3.Ch09
