import Mathlib

/-!
# LeanZju D3 Demo

This file supports the classroom slides for D3.  It is intentionally written as
an executable script for live teaching:

* inspect types and theorem statements before proving;
* build concrete `instance`s for `AddGroup`, `Group`, `Ring`, `Field`, and `Category`;
* see how proposition instances such as `Fact P` are passed automatically;
* compare AI-generated Lean drafts with corrected, kernel-checked code.
-/

namespace LeanZju


/-!
## 1. Inspect first

The first classroom habit is to ask Lean what structure, notation, and theorem
names already mean.
-/

#check Group
#check AddGroup
#check AddCommGroup
#check Ring
#check Field
#check Module
#check CategoryTheory.Category
#check Subtype
#check Subgroup
#check Subring
#check Submodule
#check Fact
#check inferInstance

example (a b : ℝ) (h : a ≤ b) : 0 ≤ b - a := by
  linarith

example : (2 : Nat) + 2 = 4 := by
  decide

example (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

/-!
## 2. AddGroup versus Group

`AddGroup` and `Group` express the same algebraic pattern with different
notation.  `AddGroup A` uses `0`, `+`, and unary minus; `Group G` uses `1`,
`*`, and inverse.  Many additive facts are generated from multiplicative ones
by Mathlib's `to_additive` machinery, but in everyday proofs the notations tell
Lean which typeclass to search for.
-/

section AddGroupVsGroup

#check AddGroup
#check Group
#check neg_add_cancel
#check inv_mul_cancel

example (A : Type*) [AddGroup A] (a : A) : -a + a = 0 := by
  exact neg_add_cancel a

example (G : Type*) [Group G] (g : G) : g⁻¹ * g = 1 := by
  exact inv_mul_cancel g

example (A : Type*) [AddGroup A] (a b c : A) :
    (a + b) + c = a + (b + c) := by
  exact add_assoc a b c

example (G : Type*) [Group G] (a b c : G) :
    (a * b) * c = a * (b * c) := by
  exact mul_assoc a b c

#synth AddGroup ℤ

example (a : ℤ) : -a + a = 0 := by
  exact neg_add_cancel a

end AddGroupVsGroup

/-!
## 3. Subtype: elements carrying a proof

A subtype `{x : α // p x}` stores both a value `x : α` and a proof that the
value satisfies the predicate `p`.  This is the basic shape behind many
subobjects in Mathlib.
-/

section SubtypeBasics

def NonzeroInt := {n : ℤ // n ≠ 0}

example : NonzeroInt :=
  ⟨1, by norm_num⟩

example (x : NonzeroInt) : ℤ :=
  x.1

example (x : NonzeroInt) : x.1 ≠ 0 :=
  x.2

example (x : NonzeroInt) : x.1 ≠ 0 :=
  x.property

#check Subtype.val
#check Subtype.property

end SubtypeBasics

/-!
## 4. Group instance: a two-element sign group

To build a `Group`, Lean needs operations and laws.  In this finite example the
laws are checked by case splitting.
-/

inductive Sign where
  | pos
  | neg
  deriving DecidableEq, Repr

open Sign

instance : Group Sign where
  mul a b :=
    match a, b with
    | pos, x => x
    | neg, pos => neg
    | neg, neg => pos
  one := pos
  inv a := a
  mul_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  one_mul := by
    intro a
    cases a <;> rfl
  mul_one := by
    intro a
    cases a <;> rfl
  inv_mul_cancel := by
    intro a
    cases a <;> rfl

#eval pos * neg
#eval neg * neg

#synth Group Sign
#check mul_assoc
#check one_mul
#check mul_one
#check inv_mul_cancel

example (a b c : Sign) : (a * b) * c = a * (b * c) := by
  exact mul_assoc a b c

example (a : Sign) : a⁻¹ * a = 1 := by
  exact inv_mul_cancel a

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

/-!
## 6. Ring instance: transport a known ring structure

Writing a full `CommRing` instance by hand requires many fields.  A common
Mathlib pattern is to transport structure along an equivalence, then still use
the resulting ring laws one by one.
-/

@[ext]
structure PairInt where
  x : Int
  y : Int
  deriving DecidableEq, Repr

namespace PairInt

def equivProd : PairInt ≃ Int × Int where
  toFun p := (p.x, p.y)
  invFun q := ⟨q.1, q.2⟩
  left_inv := by
    intro p
    ext <;> rfl
  right_inv := by
    intro q
    cases q
    rfl

instance : CommRing PairInt := equivProd.commRing

#synth Ring PairInt
#synth CommRing PairInt
#check add_assoc
#check zero_add
#check neg_add_cancel
#check left_distrib
#check right_distrib
#check mul_assoc
#check mul_comm

example (p q : PairInt) :
    p + q = ⟨p.x + q.x, p.y + q.y⟩ := by
  rfl

example (p q : PairInt) :
    p * q = ⟨p.x * q.x, p.y * q.y⟩ := by
  rfl

example (p q r : PairInt) :
    p * (q + r) = p * q + p * r := by
  exact mul_add p q r

example (p : PairInt) : -p + p = 0 := by
  exact neg_add_cancel p

example (p q : PairInt) : p * q = q * p := by
  exact mul_comm p q

example (p q : PairInt) :
    (p + q) ^ 2 = p ^ 2 + 2 * p * q + q ^ 2 := by
  ring

end PairInt

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

lemma xComponent_add (w1 w2 : W) :
    xComp (w1 + w2) = xComp w1 + xComp w2 := by
    -- Advanced exercise: this requires extra uniqueness/linearity data for the
    -- chosen decomposition.  We keep it as a classroom discussion point.
    sorry

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



/-!
## 11. Category instance: the one-object one-arrow category

To build a category, Lean asks for morphisms, identities, composition, and the
three category laws.
-/

section CategoryInstance

open CategoryTheory
open CategoryTheory.Limits

#check CategoryTheory.CategoryStruct
#check CategoryTheory.Category
#check CategoryTheory.CategoryStruct.comp
#check CategoryTheory.Category.id_comp
#check CategoryTheory.Category.comp_id
#check CategoryTheory.Category.assoc

inductive OneObj where
  | star
  deriving DecidableEq, Repr

instance : Category OneObj where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  id_comp := by
    intro X Y f
    cases f
    rfl
  comp_id := by
    intro X Y f
    cases f
    rfl
  assoc := by
    intro W X Y Z f g h
    cases f
    cases g
    cases h
    rfl

#synth Category OneObj
#check Functor
#check NatTrans
#check CategoryTheory.Functor.map
#check CategoryTheory.Functor.map_id
#check CategoryTheory.Functor.map_comp
#check CategoryTheory.NatTrans.naturality

example (X Y : OneObj) (f : X ⟶ Y) : 𝟙 X ≫ f = f := by
  exact Category.id_comp f

example (W X Y Z : OneObj) (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := by
  exact Category.assoc f g h

variable (C D E : Type*) [Category C] [Category D] [Category E]

example (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E :=
  F ⋙ G

example (F G : C ⥤ D) : Type _ :=
  F ⟶ G

example (F G : C ⥤ D) (η : F ⟶ G) (X : C) : F.obj X ⟶ G.obj X :=
  η.app X

#check HomologicalComplex
#check ChainComplex
#check CochainComplex
#check HomologicalComplex.X
#check HomologicalComplex.d
#check HomologicalComplex.shape
#check HomologicalComplex.d_comp_d'
#check HomologicalComplex.d_comp_d

noncomputable def tinyZeroComplex :
    HomologicalComplex (Discrete PUnit) (ComplexShape.up ℕ) where
  X _ := Discrete.mk PUnit.unit
  d _ _ := 0
  shape := by
    intro i j hij
    rfl
  d_comp_d' := by
    intro i j k hij hjk
    simp

#check tinyZeroComplex.X
#check tinyZeroComplex.d

example (i j : ℕ) : tinyZeroComplex.d i j = 0 := by
  rfl

example (i j k : ℕ) : tinyZeroComplex.d i j ≫ tinyZeroComplex.d j k = 0 := by
  exact HomologicalComplex.d_comp_d tinyZeroComplex i j k

end CategoryInstance

/-!
## 12. Proposition instances

Some typeclasses live in `Prop`.  They are not data structures with
computational content; they are automatically available proofs or properties.
-/

section PropositionInstances

instance : Fact (2 ≤ 5) := ⟨by norm_num⟩

example : 2 ≤ 5 := by
  exact Fact.out

example (n : Nat) [Fact (n ≠ 0)] : 0 < n := by
  exact Nat.pos_of_ne_zero (Fact.out : n ≠ 0)

class IsEven (n : Nat) : Prop where
  witness : ∃ k, n = 2 * k

instance : IsEven 8 where
  witness := ⟨4, by norm_num⟩

example [h : IsEven n] : ∃ k, n = 2 * k := by
  exact h.witness

example : ∃ k, 8 = 2 * k := by
  exact (inferInstance : IsEven 8).witness

end PropositionInstances

/-!
## 13. More Lean: instance search, local instances, and theorem reuse
-/

section DeeperLean

#check inferInstance
#check (inferInstance : Group Sign)

example : Group Sign := by
  infer_instance

example : CommRing PairInt := by
  infer_instance

example : Field WrappedQ := by
  infer_instance

example : 2 ≤ 5 := by
  haveI : Fact (2 ≤ 5) := ⟨by norm_num⟩
  exact Fact.out

example {G : Type*} [Group G] (a b : G) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  group

example {R : Type*} [CommRing R] (a b c d : R)
    (h1 : c = d * a + b) (h2 : b = a * d) :
    c = 2 * a * d := by
  rw [h1, h2]
  ring

end DeeperLean

/-!
## 14. Small combinatorics examples for `decide`, `simp`, and `ring`
-/

section FinsetAndGraph

open BigOperators
open Finset

#check Finset.range
#check Finset.card_range
#check Finset.filter
#check Finset.sum_range_succ

example : (Finset.range 5).card = 5 := by
  exact Finset.card_range 5

example : ((Finset.range 6).filter fun n => n % 2 = 0).card = 3 := by
  native_decide

example (n : Nat) : ∑ _i ∈ Finset.range (n + 1), (1 : Nat) = n + 1 := by
  simp

theorem sum_id (n : Nat) :
    ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) / 2 := by
  symm
  apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add 2, ← ih]
      ring

example : ∑ i ∈ Finset.range 5, i = 10 := by
  norm_num [sum_id]

def path3 : SimpleGraph (Fin 3) where
  Adj i j :=
    (i = 0 ∧ j = 1) ∨
    (i = 1 ∧ j = 0) ∨
    (i = 1 ∧ j = 2) ∨
    (i = 2 ∧ j = 1)
  symm := by
    unfold Symmetric
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  loopless := by
    constructor
    intro i h
    fin_cases i <;> simp_all

example : path3.Adj 0 1 := by
  simp [path3]

example : path3.Adj 1 2 := by
  simp [path3]

example : ¬ path3.Adj 0 2 := by
  simp [path3]

example (i : Fin 3) : ¬ path3.Adj i i := by
  fin_cases i <;> simp [path3]

example : (⊤ : SimpleGraph (Fin 3)).Adj 0 1 := by
  decide

example (i j : Fin 3) (h : path3.Adj i j) : i ≠ j := by
  exact SimpleGraph.ne_of_adj path3 h

example : path3.Adj 0 1 ∧ ¬ path3.Adj 0 2 := by
  constructor
  · simp [path3]
  · simp [path3]

example : (⊤ : SimpleGraph (Fin 4)).Adj 0 3 := by
  decide

end FinsetAndGraph

/-!
## 15. AI-assisted Lean: bad drafts and corrected code

The important classroom point is diagnostic: many AI errors are statement
errors, missing instance assumptions, or API hallucinations rather than just
tactic errors.
-/

section AIExamples

/-!
Bad draft: the statement is false at `x = 0`.

```lean
example (K : Type*) [Field K] (x : K) : x / x = 1 := by
  field_simp
```
-/

example (K : Type*) [Field K] (x : K) (hx : x ≠ 0) : x / x = 1 := by
  field_simp [hx]

/-!
Bad draft: the order of inverses is wrong in a noncommutative group.

```lean
example (G : Type*) [Group G] (a b : G) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  group
```
-/

example (G : Type*) [Group G] (a b : G) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  group

example (A : Type*) [CommGroup A] (a b : A) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  rw [mul_inv_rev]
  exact mul_comm b⁻¹ a⁻¹

/-!
Bad draft: a plausible theorem name that does not exist.

```lean
example : (Finset.range 5).card = 5 := by
  exact Finset.card_range_five
```
-/

#check Finset.card_range

example : (Finset.range 5).card = 5 := by
  exact Finset.card_range 5

/-!
Bad draft: `decide` is not arbitrary classical reasoning.

```lean
example (P : Prop) : P ∨ ¬ P := by
  decide
```
-/

example (P : Prop) [Decidable P] : P ∨ ¬ P := by
  by_cases h : P
  · exact Or.inl h
  · exact Or.inr h

example (P : Prop) : P ∨ ¬ P := by
  classical
  exact em P

/-!
Bad draft: the theorem is specialized to real numbers even though Mathlib has
a more reusable typeclass formulation.
-/

#check add_le_add_right

example {α : Type*} [Add α] [LE α] [AddLeftMono α]
    {a b : α} (h : a ≤ b) (c : α) :
    c + a ≤ c + b := by
  exact add_le_add_right h c

end AIExamples


end LeanZju
