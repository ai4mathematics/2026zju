/-
  D2_InductionProofs.lean

  Live demo file for `cases` and `induction`.
-/

namespace D2InductionProofs

/-! ## Case splitting -/

example (b : Bool) : b = true \/ b = false := by
  cases b <;> simp

example {alpha : Type} (x : Option alpha) :
    x = none \/ Exists fun a => x = some a := by
  cases x with
  | none =>
      exact Or.inl rfl
  | some a =>
      exact Or.inr (Exists.intro a rfl)

/-!
Instructor prompt:
How many goals should `cases x` create when `x : Option alpha`?
-/

/-! ## Induction on natural numbers: addition -/

def add (m : Nat) : Nat -> Nat
  | 0 => m
  | n + 1 => add m n + 1

theorem add_zero (m : Nat) : add m 0 = m := by
  rfl

theorem add_succ (m n : Nat) : add m (n + 1) = add m n + 1 := by
  rfl

theorem zero_add (n : Nat) : add 0 n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        add 0 (n + 1) = add 0 n + 1 := rfl
        _ = n + 1 := by rw [ih]

theorem add_assoc (a b c : Nat) :
    add (add a b) c = add a (add b c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        add (add a b) (c + 1) = add (add a b) c + 1 := rfl
        _ = add a (add b c) + 1 := by rw [ih]
        _ = add a (add b (c + 1)) := rfl

/-! ## Induction on lists -/

theorem append_nil_right {alpha : Type} (xs : List alpha) :
    xs ++ [] = xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      calc
        (x :: xs) ++ [] = x :: (xs ++ []) := rfl
        _ = x :: xs := by rw [ih]

theorem length_append {alpha : Type} (xs ys : List alpha) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.add_assoc, Nat.add_comm]

theorem map_id_list {alpha : Type} (xs : List alpha) :
    List.map (fun x => x) xs = xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [ih]

/-! ## Induction on a custom tree type -/

inductive Tree (alpha : Type) where
  | leaf : alpha -> Tree alpha
  | node : Tree alpha -> Tree alpha -> Tree alpha
  deriving Repr, BEq

def mirror {alpha : Type} : Tree alpha -> Tree alpha
  | Tree.leaf x => Tree.leaf x
  | Tree.node left right => Tree.node (mirror right) (mirror left)

theorem mirror_mirror {alpha : Type} (t : Tree alpha) :
    mirror (mirror t) = t := by
  induction t with
  | leaf x =>
      rfl
  | node left right ihLeft ihRight =>
      simp [mirror, ihLeft, ihRight]

/-!
Exercise ideas:
1. Prove a theorem about recursively defined addition.
2. Prove a list theorem where the base case is solved by `rfl`.
3. In the step case, explain what the induction hypothesis says.
4. Prove a theorem about `Tree` using two induction hypotheses.
-/

end D2InductionProofs
