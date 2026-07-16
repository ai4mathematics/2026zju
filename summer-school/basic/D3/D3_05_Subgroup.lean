import Mathlib

/-! Requires a configured Mathlib Lake project; see `README.md` in this folder. -/

/-!
# D3_05_Subgroup

Standalone file extracted from `D3_Demo.lean` for classroom navigation.
-/

namespace LeanZjuD3.Ch05

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

def posSubgroup : Subgroup Sign where
  carrier := {g | g = Sign.pos}
  one_mem' := by
    rfl
  mul_mem' := by
    intro a b ha hb
    rw [ha, hb]
    rfl
  inv_mem' := by
    intro a ha
    rw [ha]
    rfl

/-!
`group_1` and `group_2` live on different types.  To regard the first group as
a subgroup of the second, we give an injective homomorphism and take its range.
The multiplicative operation on these tagged types is addition underneath.
-/

def IntegerGroup := Multiplicative ℤ
def RationalGroup := Multiplicative ℚ

instance group_1 : Group IntegerGroup := Multiplicative.group
instance group_2 : Group RationalGroup := Multiplicative.group

def intToRat : IntegerGroup →* RationalGroup :=
  show Multiplicative ℤ →* Multiplicative ℚ from
    (Int.castAddHom ℚ).toMultiplicative

example (m n : IntegerGroup) :
    intToRat (m * n) = intToRat m * intToRat n := by
  exact map_mul intToRat m n

theorem intToRat_injective : Function.Injective intToRat := by
  change Function.Injective ((Int.castAddHom ℚ).toMultiplicative)
  intro m n h
  apply Multiplicative.toAdd.injective
  have h' : (m.toAdd : ℚ) = (n.toAdd : ℚ) := by
    simpa using congrArg Multiplicative.toAdd h
  exact_mod_cast h'

def integerRange : Subgroup RationalGroup := intToRat.range

example : Group integerRange := by
  infer_instance

noncomputable def group_1_as_subgroup : IntegerGroup ≃* intToRat.range :=
  MonoidHom.ofInjective intToRat_injective

#check Subgroup.subtype
#check MonoidHom.range
#check MonoidHom.ofInjective

example : Sign.pos ∈ posSubgroup := by
  rfl

example (x : posSubgroup) : (x : Sign) = Sign.pos := by
  exact x.property

example : Group posSubgroup := by
  infer_instance

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
