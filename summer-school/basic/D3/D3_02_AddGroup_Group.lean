import Mathlib

/-! Requires a configured Mathlib Lake project; see `README.md` in this folder. -/

/-!
# D3_02_AddGroup_Group

Standalone file extracted from `D3_Demo.lean` for classroom navigation.
-/

namespace LeanZjuD3.Ch02

/-!
## 2. Structure inheritance with `extends`

The declaration `class Child extends Parent` reuses the fields of `Parent` and
creates a projection from the child structure back to the parent.  Mathlib
registers these parent projections for typeclass search.  Therefore an
`AddSemigroup G` can be used whenever Lean asks for `Add G`, but an arbitrary
`Add G` cannot be promoted to `AddSemigroup G`: the associativity proof is still
missing.
-/

section Extends

#check Add
#check AddSemigroup
#check AddSemigroup.toAdd
#check AddMonoid.toAddSemigroup
#check AddMonoid.toAddZeroClass

example (G : Type*) [AddSemigroup G] : Add G := by
  infer_instance

example (G : Type*) [AddMonoid G] : AddSemigroup G := by
  infer_instance

example (G : Type*) [AddMonoid G] : AddZeroClass G := by
  infer_instance

end Extends

/-!
## The `Group` class in Mathlib

The multiplicative hierarchy continues as `Monoid`, `DivInvMonoid`, and then
`Group`. A `Group G` therefore supplies the parent interfaces automatically.
The field `Group.inv_mul_cancel` is the stored axiom; the unprotected theorem
`inv_mul_cancel` is the convenient public theorem used in ordinary proofs.
-/

section GroupClass

#check Monoid
#check DivInvMonoid
#check Group.toDivInvMonoid
#check Group.inv_mul_cancel
#check inv_mul_cancel

example (G : Type*) [Group G] : Monoid G := by
  infer_instance

example (G : Type*) [Group G] : DivInvMonoid G := by
  infer_instance

example (G : Type*) [Group G] (a : G) : a⁻¹ * a = 1 := by
  exact inv_mul_cancel a

end GroupClass

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
## 2.1 From `Add` to `AddGroup` in Mathlib

The source hierarchy separates raw notation, algebraic laws, identity data,
natural and integer scalar multiplication, and inverse laws.  In practice,
`AddGroup.ofLeftAxioms` fills the engineering fields from three mathematical
proofs: associativity, the left zero law, and the left inverse law.
-/

section FromAddToAddGroup

#check Add
#check AddSemigroup
#check AddZeroClass
#check AddMonoid
#check SubNegMonoid
#check AddGroup
#check AddGroup.ofLeftAxioms

/-!
### `nsmul` and `zsmul`

For an additive monoid, `nsmul` interprets `n • a` as repeated addition by a
natural number. Once negation is available, `zsmul` extends this operation to
integer coefficients. Mathlib stores these operations in the class hierarchy
so that all inheritance paths reuse definitionally the same scalar action.
-/

#check AddMonoid.nsmul
#check nsmulRec
#check zero_nsmul
#check succ_nsmul
#check SubNegMonoid.zsmul
#check zsmulRec
#check zero_zsmul
#check negSucc_zsmul

example (M : Type*) [AddMonoid M] : SMul ℕ M := by
  infer_instance

example (G : Type*) [SubNegMonoid G] : SMul ℤ G := by
  infer_instance

example : (3 : ℕ) • (5 : ℤ) = 15 := by
  norm_num

example : (-3 : ℤ) • (5 : ℤ) = -15 := by
  norm_num

/-!
### Instance diamonds

An instance diamond occurs when typeclass search can synthesize the same
data-carrying target class through two paths. Priorities can select a path, but
they do not make the results definitionally equal. This deliberately bad
hierarchy constructs natural scalar multiplication by two recursive routes.
-/

namespace InstanceDiamondDemo

class NsmulData (α : Type*) where
  nsmul : ℕ → α → α

class ZsmulData (α : Type*) where
  zsmul : ℤ → α → α

class BadAddMonoid (α : Type*) extends Add α, Zero α, NsmulData α

class BadAddGroup (α : Type*) extends Add α, Zero α, Neg α

def repeatAddRight {α : Type*} [Add α] [Zero α] : ℕ → α → α
  | 0, _ => 0
  | n + 1, x => x + repeatAddRight n x

def repeatAddLeft {α : Type*} [Add α] [Zero α] : ℕ → α → α
  | 0, _ => 0
  | n + 1, x => repeatAddLeft n x + x

instance groupToMonoid [BadAddGroup α] : BadAddMonoid α where
  nsmul := repeatAddRight

def groupZsmul {α : Type*} [BadAddGroup α] : ℤ → α → α
  | Int.ofNat n, x => repeatAddLeft n x
  | Int.negSucc n, x => -(repeatAddLeft n.succ x)

instance groupToZsmul [BadAddGroup α] : ZsmulData α where
  zsmul := groupZsmul

instance (priority := 90) nsmulFromZsmul [ZsmulData α] : NsmulData α where
  nsmul n x := ZsmulData.zsmul (n : ℤ) x

@[ext]
structure Token where
  value : ℤ
deriving Repr, DecidableEq

instance : BadAddGroup Token where
  add x y := ⟨x.value + y.value⟩
  zero := ⟨0⟩
  neg x := ⟨-x.value⟩

#synth BadAddMonoid Token
#synth ZsmulData Token
#synth NsmulData Token

#eval (repeatAddRight 2 (Token.mk 3)).value
#eval (groupZsmul (2 : ℤ) (Token.mk 3)).value

example (x : Token) :
    repeatAddRight 2 x = groupZsmul (2 : ℤ) x := by
  fail_if_success rfl
  apply Token.ext
  change x.value + (x.value + 0) = (0 + x.value) + x.value
  simp

end InstanceDiamondDemo

/-!
Mathlib avoids this problem for natural scalar multiplication by storing
`nsmul` in `AddMonoid` and reusing it along every inheritance path. The first
example below is definitional equality: it closes with `rfl`.
-/

#synth SMul ℕ (Polynomial ℕ)

example (n : ℕ) (p : Polynomial ℕ) :
    AddMonoid.nsmul n p = n • p := by
  rfl

example (p : Polynomial ℕ) : (2 : ℕ) • p = p + p := by
  simpa using two_nsmul p

@[ext]
structure WrappedInt where
  val : ℤ

instance : Add WrappedInt where
  add a b := ⟨a.val + b.val⟩

instance : Zero WrappedInt where
  zero := ⟨0⟩

instance : Neg WrappedInt where
  neg a := ⟨-a.val⟩

instance : AddGroup WrappedInt :=
  AddGroup.ofLeftAxioms
    (fun a b c => by
      apply WrappedInt.ext
      exact add_assoc a.val b.val c.val)
    (fun a => by
      apply WrappedInt.ext
      exact zero_add a.val)
    (fun a => by
      apply WrappedInt.ext
      exact neg_add_cancel a.val)

#synth Add WrappedInt
#synth AddSemigroup WrappedInt
#synth AddZeroClass WrappedInt
#synth AddMonoid WrappedInt
#synth SubNegMonoid WrappedInt
#synth AddGroup WrappedInt
#synth AddCancelMonoid WrappedInt
#synth SubtractionMonoid WrappedInt

#check add_zero
#check add_neg_cancel
#check sub_self
#check neg_add_rev
#check add_left_cancel

example (a b : WrappedInt) : a - b = a + -b := by
  exact sub_eq_add_neg a b

example (a : WrappedInt) : -a + a = 0 := by
  exact neg_add_cancel a

example (a : WrappedInt) : a + -a = 0 := by
  exact add_neg_cancel a

end FromAddToAddGroup

end LeanZjuD3.Ch02
