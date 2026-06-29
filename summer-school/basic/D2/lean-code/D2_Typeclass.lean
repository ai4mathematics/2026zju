/-
  D2_Typeclass.lean

  Core type class demo without mathlib.
  This file explains the mechanism first, then shows algebraic notation classes
  that are available in Lean's core environment.
-/

namespace D2Typeclass

/-! ## A tiny custom mathematical type class -/

class HasNorm (alpha : Type) where
  norm : alpha -> Nat

def doubleNorm {alpha : Type} [HasNorm alpha] (x : alpha) : Nat :=
  2 * HasNorm.norm x

/-! ## Instances -/

structure Vector2 where
  x : Int
  y : Int
  deriving Repr, BEq, DecidableEq

def intAbsNat (z : Int) : Nat :=
  if z < 0 then Int.toNat (-z) else Int.toNat z

instance : HasNorm Vector2 where
  norm v := intAbsNat v.x + intAbsNat v.y

instance : HasNorm Nat where
  norm n := n

#synth HasNorm Vector2
#synth HasNorm Nat

#eval doubleNorm ({ x := -3, y := 4 } : Vector2)
#eval doubleNorm (7 : Nat)

/-!
The square brackets in `[HasNorm alpha]` ask Lean to find an instance.
This is the same mechanism behind algebraic notation such as `+` and `*`.
-/

/-! ## Built-in algebraic notation classes -/

#synth Add Nat
#synth Add Int
#synth Mul Nat
#synth Mul Int
#synth OfNat Nat 2
#synth OfNat Int 2

#eval (3 : Nat) + 4
#eval (3 : Int) + (-4)
#eval (3 : Nat) * 4
#eval (3 : Int) * (-4)

def addThree {alpha : Type} [Add alpha] (a b c : alpha) : alpha :=
  a + b + c

#eval addThree (1 : Nat) 2 3
#eval addThree (1 : Int) 2 3

/-!
Important distinction:

`[Add alpha]` gives Lean a notation and operation.
It does not by itself say that addition is associative or commutative.

For algebraic laws, we use stronger mathematical classes such as semigroups,
monoids, rings, and fields. Those are especially rich in mathlib.
-/

/-! ## Deriving remains useful for custom finite types -/

inductive Color where
  | red | green | blue
  deriving Repr, BEq, DecidableEq

#synth Repr Color
#synth BEq Color
#synth DecidableEq Color

#eval Color.red
#eval Color.red == Color.blue
#eval Color.green == Color.green

example : Decidable (Color.red = Color.blue) :=
  inferInstance

/-! ## Ordinary implicit parameters vs type class parameters -/

def useExplicit {alpha : Type} (inst : HasNorm alpha) (x : alpha) : Nat :=
  inst.norm x

def useInstance {alpha : Type} [HasNorm alpha] (x : alpha) : Nat :=
  HasNorm.norm x

#eval useExplicit (inferInstance : HasNorm Nat) 5
#eval useInstance (5 : Nat)

/-!
Exercise ideas:
1. Define a new structure and give it a `HasNorm` instance.
2. Use `#synth` to check whether Lean can find the instance.
3. Write a generic function using `[Add alpha]`.
4. Explain why `[Add alpha]` is weaker than a ring or field structure.
-/

end D2Typeclass
