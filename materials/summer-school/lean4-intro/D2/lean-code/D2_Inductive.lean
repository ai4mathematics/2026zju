/-
  D2_Inductive.lean

  Teaching goal:
  An inductive declaration tells Lean all the ways to build values of a type.
  The same declaration also explains how to consume those values later by
  pattern matching, recursion, and induction.
-/

namespace D2Inductive

/-!
## 0. The guiding picture

When teaching an inductive type, ask three questions:

1. What is the new type?
2. What are its constructors?
3. Do any constructors carry data or refer recursively to the same type?

The answer to these questions predicts the programs and proofs we can write.
-/

/-! ## 1. A finite type: all values are listed explicitly -/

inductive Weekday where
  | mon | tue | wed | thu | fri | sat | sun
  deriving Repr, BEq, DecidableEq

#check Weekday
#check Weekday.mon
#check Weekday.sun

#eval Weekday.mon
#eval Weekday.sat == Weekday.sun
#eval Weekday.sat == Weekday.sat

def allWeekdays : List Weekday :=
  [ Weekday.mon, Weekday.tue, Weekday.wed, Weekday.thu
  , Weekday.fri, Weekday.sat, Weekday.sun ]

#eval allWeekdays

/-!
Instructor prompt:
This is a "closed world": every `Weekday` is one of the seven constructors.
There is no hidden eighth weekday.
-/

/-! ## 2. Constructors are functions: natural numbers -/

inductive MyNat where
  | zero : MyNat
  | succ : MyNat -> MyNat
  deriving Repr, BEq

#check MyNat.zero
#check MyNat.succ

def one : MyNat :=
  MyNat.succ MyNat.zero

def two : MyNat :=
  MyNat.succ one

#eval MyNat.zero
#eval one
#eval two

/-!
Observation:
`zero` is already a natural number.
`succ` is a function: it needs a smaller natural number before it produces a
new natural number.
-/

/-! ## 3. Type parameters versus constructor arguments -/

inductive MyOption (alpha : Type) where
  | none : MyOption alpha
  | some : alpha -> MyOption alpha
  deriving Repr, BEq

#check MyOption.none
#check MyOption.some

#check (MyOption.none : MyOption Nat)
#check (MyOption.none : MyOption String)
#check (MyOption.some : Nat -> MyOption Nat)
#check (MyOption.some : String -> MyOption String)

def missingNumber : MyOption Nat :=
  MyOption.none

def foundNumber : MyOption Nat :=
  MyOption.some 42

def foundName : MyOption String :=
  MyOption.some "Ada"

#eval missingNumber
#eval foundNumber
#eval foundName

/-!
Instructor prompt:
The parameter `alpha` changes the whole family of types:

  MyOption Nat
  MyOption String
  MyOption Weekday

The constructor argument is the data stored by a particular constructor.
-/

/-! ## 4. A recursive definition suggested by MyNat -/

namespace MyNat

def add : MyNat -> MyNat -> MyNat
  | m, zero => m
  | m, succ n => succ (add m n)

#eval add two MyNat.zero
#eval add two one
#eval add two two

theorem add_zero (m : MyNat) : add m zero = m := by
  rfl

theorem add_succ (m n : MyNat) : add m (succ n) = succ (add m n) := by
  rfl

end MyNat

/-!
The recursive constructor suggests the recursive definition:

  add m zero     = m
  add m (succ n) = succ (add m n)

This is the bridge from inductive data to recursive mathematical definitions.
-/

/-! ## 5. Recursive data: lists -/

inductive MyList (alpha : Type) where
  | nil : MyList alpha
  | cons : alpha -> MyList alpha -> MyList alpha
  deriving Repr, BEq

#check MyList.nil
#check MyList.cons
#check (MyList.nil : MyList Nat)
#check (MyList.cons : Nat -> MyList Nat -> MyList Nat)

def smallList : MyList Nat :=
  MyList.cons 1 (MyList.cons 2 (MyList.cons 3 MyList.nil))

#eval smallList

/-!
The two possible shapes of a list are:

1. empty;
2. a head element together with a smaller tail list.

This is why recursive list functions usually have exactly these two branches.
-/

/-! ## 6. Recursive data with more than one recursive subobject -/

inductive Tree (alpha : Type) where
  | leaf : alpha -> Tree alpha
  | node : Tree alpha -> Tree alpha -> Tree alpha
  deriving Repr, BEq

#check Tree.leaf
#check Tree.node
#check (Tree.leaf : Nat -> Tree Nat)
#check (Tree.node : Tree Nat -> Tree Nat -> Tree Nat)

def sampleTree : Tree Nat :=
  Tree.node
    (Tree.leaf 1)
    (Tree.node (Tree.leaf 2) (Tree.leaf 3))

#eval sampleTree

/-!
Instructor prompt:
A tree node has two recursive subobjects. Later, an induction proof over trees
will usually have two induction hypotheses in the node case.
-/

/-! ## 7. What Lean generates: recursors -/

#check Weekday.rec
#check MyOption.rec
#check MyNat.rec
#check MyList.rec
#check Tree.rec

/-!
We do not teach recursors in detail here.

But these `#check` lines are useful because they reveal the deeper point:
an inductive declaration gives Lean a general elimination principle.

That principle later appears in friendly forms:

* `match` for programs,
* structural recursion for recursive functions,
* `cases` for proof by cases,
* `induction` for induction proofs.
-/

/-! ## 8. Student checkpoint -/

inductive TrafficLight where
  | red | yellow | green
  deriving Repr, BEq, DecidableEq

#check TrafficLight.red
#eval TrafficLight.red == TrafficLight.green

/-!
Quick questions:

1. What is the type being defined?
2. What are the constructors?
3. Which constructors carry data?
4. Is the type recursive?
5. How many cases should a function on this type have?

Exercise ideas:

1. Define a `Direction` type with four constructors.
2. Define a `MaybePair alpha` type with constructors `none` and
   `pair : alpha -> alpha -> MaybePair alpha`.
3. Define a binary tree type whose leaves store no data but nodes store a value.
-/

end D2Inductive
