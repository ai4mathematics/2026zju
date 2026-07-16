import Mathlib

/-! Requires a configured Mathlib Lake project; see `README.md` in this folder. -/

/-!
# D3_10_VectorSpace_Choose

Standalone file extracted from `D3_Demo.lean` for classroom navigation.
-/

namespace LeanZjuD3.Ch10

/-!
## 10. An example of a symplectic vector space

Let K be a field . Consider a finite dimensional K-vector space V of dimension 2n equipped with a non-degenerate symplectic form <,>. Fix a complete polarization of V, i.e., a decomposition V = X ⊕ Y where X and Y are maximal isotropic subspaces.
-/

/-！
AI version
-/


variable (F W : Type*)
variable [Field F] [Fintype F]
variable [AddCommGroup W] [Module F W] [FiniteDimensional F W]

/-- The symplectic form is alternating. -/
def IsAlternating (ω : W →ₗ[F] W →ₗ[F] F) : Prop :=
  ∀ w : W, ω w w = 0

/-- The symplectic form is nondegenerate. -/
def IsNondegenerate (ω : W →ₗ[F] W →ₗ[F] F) : Prop :=
  ∀ w : W, (∀ v : W, ω w v = 0) → w = 0

/-- A subspace is totally isotropic for `ω`. -/
def TotallyIsotropic
    (ω : W →ₗ[F] W →ₗ[F] F) (U : Submodule F W) : Prop :=
  ∀ u : W, u ∈ U → ∀ v : W, v ∈ U → ω u v = 0

/-- A complete polarization `W = X ⊕ Y` by two totally isotropic subspaces. -/
structure CompletePolarization
    (ω : W →ₗ[F] W →ₗ[F] F) where
  X : Submodule F W
  Y : Submodule F W
  isotropic_X : TotallyIsotropic F W ω X
  isotropic_Y : TotallyIsotropic F W ω Y
  disjoint : Disjoint X Y
  sup_eq_top : X ⊔ Y = ⊤

omit [Fintype F] [FiniteDimensional F W] in
lemma exists_decomposition (P : CompletePolarization F W ω) (w : W) :
    ∃ x : W, x ∈ P.X ∧ ∃ y : W, y ∈ P.Y ∧ w = x + y := by
  have hw : w ∈ P.X ⊔ P.Y := by
    rw [P.sup_eq_top]
    exact Submodule.mem_top
  rcases Submodule.mem_sup.mp hw with ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy, hxy.symm⟩


/-!
Consider the decomposition of a vector w ∈ W into its components in X and Y. We can define the x-component and y-component of w with respect to the complete polarization P.
-/

variable (ω : W →ₗ[F] W →ₗ[F] F) (P : CompletePolarization F W ω)

noncomputable def xComponent
     (w : W) : W := Classical.choose (exists_decomposition F W P w)

omit [Fintype F] [FiniteDimensional F W] in
lemma xComponent_mem
    (P : CompletePolarization F W ω) (w : W) :
    xComponent F W ω P w ∈ P.X := by
  dsimp [xComponent]
  exact (Classical.choose_spec (exists_decomposition F W P w)).1

noncomputable def yComponent
    (P : CompletePolarization F W ω) (w : W) : W :=
  Classical.choose
    ((Classical.choose_spec (exists_decomposition F W P w)).2)

omit [Fintype F] [FiniteDimensional F W] in
lemma yComponent_mem
    (P : CompletePolarization F W ω) (w : W) :
    yComponent F W ω P w ∈ P.Y := by
  dsimp [yComponent]
  exact
    (Classical.choose_spec
      ((Classical.choose_spec (exists_decomposition F W P w)).2)).1


#check xComponent F W ω P
#check yComponent F W ω P

omit [Fintype F] [FiniteDimensional F W] in
lemma decompose_by_components
    (P : CompletePolarization F W ω) (w : W) :
    w = xComponent F W ω P w + yComponent F W ω P w := by
  dsimp [xComponent, yComponent]
  exact
    (Classical.choose_spec
      ((Classical.choose_spec (exists_decomposition F W P w)).2)).2



local notation "xComp" => xComponent F W ω P
local notation "yComp" => yComponent F W ω P

omit [Fintype F] [FiniteDimensional F W] in
lemma xComponent_add (w1 w2 : W) :
    xComp (w1 + w2) = xComp w1 + xComp w2 := by
  have hx12 : xComp (w1 + w2) ∈ P.X := xComponent_mem F W ω P (w1 + w2)
  have hx1 : xComp w1 ∈ P.X := xComponent_mem F W ω P w1
  have hx2 : xComp w2 ∈ P.X := xComponent_mem F W ω P w2
  have hy12 : yComp (w1 + w2) ∈ P.Y := yComponent_mem F W ω P (w1 + w2)
  have hy1 : yComp w1 ∈ P.Y := yComponent_mem F W ω P w1
  have hy2 : yComp w2 ∈ P.Y := yComponent_mem F W ω P w2
  have hsum :
      xComp (w1 + w2) + yComp (w1 + w2) =
        (xComp w1 + xComp w2) + (yComp w1 + yComp w2) := by
    calc
      xComp (w1 + w2) + yComp (w1 + w2) = w1 + w2 :=
        (decompose_by_components F W ω P (w1 + w2)).symm
      _ = (xComp w1 + yComp w1) + (xComp w2 + yComp w2) := by
        exact congrArg₂ (· + ·)
          (decompose_by_components F W ω P w1)
          (decompose_by_components F W ω P w2)
      _ = (xComp w1 + xComp w2) + (yComp w1 + yComp w2) := by
        abel
  let z := xComp (w1 + w2) - (xComp w1 + xComp w2)
  have hzX : z ∈ P.X := P.X.sub_mem hx12 (P.X.add_mem hx1 hx2)
  have hz_eq : z = (yComp w1 + yComp w2) - yComp (w1 + w2) := by
    dsimp [z]
    calc
      xComp (w1 + w2) - (xComp w1 + xComp w2) =
          (xComp (w1 + w2) + yComp (w1 + w2)) -
            ((xComp w1 + xComp w2) + (yComp w1 + yComp w2)) +
              ((yComp w1 + yComp w2) - yComp (w1 + w2)) := by
        abel
      _ = (yComp w1 + yComp w2) - yComp (w1 + w2) := by
        rw [hsum]
        simp
  have hzY : z ∈ P.Y := by
    rw [hz_eq]
    exact P.Y.sub_mem (P.Y.add_mem hy1 hy2) hy12
  have hzBot : z ∈ (⊥ : Submodule F W) :=
    P.disjoint.le_bot ⟨hzX, hzY⟩
  have hz0 : z = 0 := by
    simpa using hzBot
  exact sub_eq_zero.mp hz0

/-！
My version
-/

variable {K : Type } [hfK : Field K]  {V : Type } [hcV : AddCommGroup V] [hmV : Module K V]

abbrev altBilinForm (B : LinearMap.BilinForm K V) :
    LinearMap.BilinForm K V :=
  B - B.flip

abbrev IsIsotropicFor
    (B : LinearMap.BilinForm K V) (X : Submodule K V) : Prop :=
  ∀ x y : X, B x y = 0

variable (B : LinearMap.BilinForm K V)
variable (X Y : Submodule K V)

class Polarization where
  iota : (X × Y) ≃ₗ[K] V
  embed : ∀ x : X, ∀ y : Y, iota ⟨x, y⟩ = x.1 + y.1
  Xisotropic : IsIsotropicFor (altBilinForm B) X
  Yisotropic : IsIsotropicFor (altBilinForm B) Y

end LeanZjuD3.Ch10
