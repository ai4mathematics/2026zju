import Mathlib

/-! Requires a configured Mathlib Lake project; see `README.md` in this folder. -/

/-!
# D3_13_Deeper_Instance_Search

Standalone file extracted from `D3_Demo.lean` for classroom navigation.
-/

namespace LeanZjuD3.Ch13


/-! Minimal prerequisites used only in this standalone chapter file. -/

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

end PairInt

@[ext]
structure WrappedQ where
  val : ℚ
  deriving DecidableEq, Repr

namespace WrappedQ

def equivRat : WrappedQ ≃ ℚ where
  toFun x := x.val
  invFun q := ⟨q⟩
  left_inv := by
    intro x
    ext
    rfl
  right_inv := by
    intro q
    rfl

instance : Field WrappedQ := equivRat.field

end WrappedQ

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

end LeanZjuD3.Ch13
