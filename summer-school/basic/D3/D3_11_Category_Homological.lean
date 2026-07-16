import Mathlib

/-! Requires a configured Mathlib Lake project; see `README.md` in this folder. -/

/-!
# D3_11_Category_Homological

Standalone file extracted from `D3_Demo.lean` for classroom navigation.
-/

namespace LeanZjuD3.Ch11

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

end LeanZjuD3.Ch11
