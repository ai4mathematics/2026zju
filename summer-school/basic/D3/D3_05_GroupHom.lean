import Mathlib

/-! Requires a configured Mathlib Lake project; see `README.md` in this folder. -/

/-!
# D3_05_GroupHom

Group homomorphisms, kernels and ranges, and the first isomorphism theorem.
This file is standalone so it can be opened directly during the lecture.
-/

namespace LeanZjuD3.Ch05Hom

/-!
## 1. A bundled group homomorphism

The notation `G →* H` means `MonoidHom G H`.  For groups, preserving `1` and
multiplication is enough: preservation of inverses and integer powers follows.
-/

section BasicHom

variable {G H : Type*} [Group G] [Group H]

def conjugationHom (g : G) : G →* G where
  toFun x := g * x * g⁻¹
  map_one' := by simp
  map_mul' := by
    intro x y
    group

example (g x y : G) : conjugationHom g (x * y) =
    conjugationHom g x * conjugationHom g y := by
  exact map_mul (conjugationHom g) x y

example (f : G →* H) (x : G) : f x⁻¹ = (f x)⁻¹ := by
  exact map_inv f x

example (f : G →* H) (x : G) (n : ℤ) : f (x ^ n) = f x ^ n := by
  exact map_zpow f x n

#check MonoidHom
#check MonoidHom.comp
#check MonoidHom.id

end BasicHom

/-!
## 2. Kernel and range

The kernel is a normal subgroup of the domain.  The range is a subgroup of the
codomain.  Normality is exactly what makes the quotient by the kernel a group.
-/

section KernelAndRange

variable {G H : Type*} [Group G] [Group H] (f : G →* H)

example (x : G) : x ∈ f.ker ↔ f x = 1 := by
  exact MonoidHom.mem_ker

example (y : H) : y ∈ f.range ↔ ∃ x : G, f x = y := by
  rfl

example : (f.ker).Normal := by
  infer_instance

#check MonoidHom.ker
#check MonoidHom.range
#check QuotientGroup.quotientKerEquivRange

end KernelAndRange

/-!
## 3. Concrete first isomorphism theorem: integers modulo five

We use multiplicative type tags so that this is literally a theorem about
`Group` and `MonoidHom`.  Underneath, multiplication is ordinary addition.
-/

def modFiveHom : Multiplicative ℤ →* Multiplicative (ZMod 5) :=
  (Int.castAddHom (ZMod 5)).toMultiplicative

example (m n : Multiplicative ℤ) :
    modFiveHom (m * n) = modFiveHom m * modFiveHom n := by
  exact map_mul modFiveHom m n

example (z : Multiplicative ℤ) :
    z ∈ modFiveHom.ker ↔ ((5 : ℕ) : ℤ) ∣ z.toAdd := by
  change ((z.toAdd : ℤ) : ZMod 5) = 0 ↔ ((5 : ℕ) : ℤ) ∣ z.toAdd
  exact ZMod.intCast_zmod_eq_zero_iff_dvd z.toAdd 5

theorem modFiveHom_surjective : Function.Surjective modFiveHom := by
  change Function.Surjective ((Int.castAddHom (ZMod 5)).toMultiplicative)
  intro y
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective y.toAdd
  refine ⟨Multiplicative.ofAdd z, ?_⟩
  apply Multiplicative.toAdd.injective
  simpa using hz

example : modFiveHom.range = ⊤ := by
  exact MonoidHom.range_eq_top.mpr modFiveHom_surjective

noncomputable def modFiveFirstIso :
    Multiplicative ℤ ⧸ modFiveHom.ker ≃* modFiveHom.range :=
  QuotientGroup.quotientKerEquivRange modFiveHom

noncomputable def modFiveFirstIsoOntoCodomain :
    Multiplicative ℤ ⧸ modFiveHom.ker ≃* Multiplicative (ZMod 5) :=
  QuotientGroup.quotientKerEquivOfSurjective modFiveHom modFiveHom_surjective

#check modFiveFirstIso
#check modFiveFirstIsoOntoCodomain

end LeanZjuD3.Ch05Hom
