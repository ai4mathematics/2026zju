import Mathlib

/-!
# D3_06_Ring_Instance

Standalone file extracted from `D3_Demo.lean` for classroom navigation.
-/

namespace LeanZjuD3.Ch06

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

end LeanZjuD3.Ch06
