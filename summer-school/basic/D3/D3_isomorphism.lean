/-！ AI Version
-/


import Mathlib

universe u v

noncomputable section

structure Iso (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

def fiberSetoid {α : Type u} {β : Type v} (f : α → β) : Setoid α where
  r := fun a b => f a = f b
  iseqv := by
    constructor
    · intro a
      rfl
    · intro a b h
      exact h.symm
    · intro a b c h1 h2
      exact h1.trans h2

def image {α : Type u} {β : Type v} (f : α → β) := {y : β // ∃ x : α, f x = y}

def toImage {α : Type u} {β : Type v} (f : α → β) :
    Quotient (fiberSetoid f) → image f :=
  Quotient.lift
    (fun a => ⟨f a, ⟨a, rfl⟩⟩)
    (by
      intro a b h
      apply Subtype.ext
      exact h)

def fromImage {α : Type u} {β : Type v} (f : α → β) :
    image f → Quotient (fiberSetoid f) :=
  fun y => Quotient.mk (fiberSetoid f) (Classical.choose y.2)

theorem toImage_fromImage {α : Type u} {β : Type v} (f : α → β) (y : image f) :
    toImage f (fromImage f y) = y := by
  rcases y with ⟨y, hy⟩
  dsimp [toImage, fromImage]
  apply Subtype.ext
  exact Classical.choose_spec hy

theorem fromImage_toImage {α : Type u} {β : Type v} (f : α → β)
    (q : Quotient (fiberSetoid f)) :
    fromImage f (toImage f q) = q := by
  refine Quotient.inductionOn q ?_
  intro a
  dsimp [toImage, fromImage]
  have h : ∃ x : α, f x = f a := ⟨a, rfl⟩
  exact Quotient.sound (Classical.choose_spec h)

def fiberQuotientIsoImage {α : Type u} {β : Type v} (f : α → β) :
    Iso (Quotient (fiberSetoid f)) (image f) where
  toFun := toImage f
  invFun := fromImage f
  left_inv := fromImage_toImage f
  right_inv := toImage_fromImage f



/-! Mathlib
-/
open Function


variable {G H : Type*} [Group G] [Group H]
variable (f : G →* H)
noncomputable def firstIsoOntoCodomain
    (hf : Function.Surjective f) :
    G ⧸ f.ker ≃* H :=
  QuotientGroup.quotientKerEquivOfSurjective f hf
