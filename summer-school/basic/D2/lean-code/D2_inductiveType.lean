/-
  D2: inductive types.
  Includes MyNat, MyOption, MyList, recursion and simple proofs.
-/

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | a, zero => a
  | a, succ b => succ (add a b)

/-- `add` with zero on the right returns the first operand. --/
theorem add_zero (a : MyNat) : add a zero = a := by
  rfl

/-- `add` with `succ b` is recursive. --/
theorem add_succ (a b : MyNat) : add a (succ b) = succ (add a b) := by
  rfl

end MyNat

inductive MyOption (α : Type) where
  | none : MyOption α
  | some : α → MyOption α

namespace MyOption

/-- Apply `f` to the value inside `MyOption`. --/
def map {α β : Type} (f : α → β) : MyOption α → MyOption β
  | none => none
  | some x => some (f x)

/-- Mapping `none` stays `none`. --/
theorem map_none {α β : Type} (f : α → β) :
  map f (none : MyOption α) = (none : MyOption β) := by
  rfl

end MyOption

inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

namespace MyList

/-- Compute the length of a `MyList`. --/
def length {α : Type} : MyList α → MyNat
  | nil => MyNat.zero
  | cons _ xs => MyNat.succ (length xs)

/-- The empty list has length zero. --/
theorem length_nil {α : Type} :
  length (MyList.nil : MyList α) = MyNat.zero := by
  rfl

/-- `cons` increases the length by one. --/
theorem length_cons {α : Type} (x : α) (xs : MyList α) :
  length (MyList.cons x xs) = MyNat.succ (length xs) := by
  rfl

end MyList
