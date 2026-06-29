/-
  D2_CommonTypes.lean

  Live demo file for common inductive types and small API examples:
  Option, List, Fin, and a mathlib-only note about Multiset.
-/

namespace D2CommonTypes

/-! ## Option: explicit failure -/

def safeHead {alpha : Type} : List alpha -> Option alpha
  | [] => none
  | x :: _ => some x

def getWithDefault {alpha : Type} (default : alpha) : Option alpha -> alpha
  | none => default
  | some x => x

#eval safeHead [1, 2, 3]
#eval safeHead ([] : List Nat)
#eval getWithDefault 0 (safeHead [7, 8, 9])
#eval getWithDefault 0 (safeHead ([] : List Nat))

#eval Option.map (fun n : Nat => n + 1) (some 4)
#eval Option.map (fun n : Nat => n + 1) none

/-!
Observation:
If a function returns `Option alpha`, code using its result must handle both
the `none` and `some` cases.
-/

/-! ## List: finite ordered data -/

#eval List.map (fun n : Nat => n + 10) [1, 2, 3]
#eval List.filter (fun n : Nat => n % 2 == 0) [1, 2, 3, 4, 5, 6]
#eval List.foldl (fun acc n : Nat => acc + n) 0 [1, 2, 3, 4]
#eval List.length [10, 20, 30]
#eval [1, 2] ++ [3, 4]

example : List.length (List.map (fun n : Nat => n + 1) [1, 2, 3]) = 3 := by
  rfl

example : List.foldl (fun acc n : Nat => acc + n) 0 [1, 2, 3] = 6 := by
  rfl

/-! ## Fin: bounded natural numbers -/

def firstOfThree : Fin 3 := 0
def lastOfThree : Fin 3 := 2

#check firstOfThree
#eval firstOfThree.val
#eval lastOfThree.val
#check firstOfThree.isLt

def letters : List String :=
  ["a", "b", "c"]

#eval letters.get (0 : Fin 3)
#eval letters.get (2 : Fin 3)

def letterVector : Vector String 3 :=
  #v["a", "b", "c"]

#eval letterVector.get (0 : Fin 3)
#eval letterVector.get (2 : Fin 3)

/-!
Try changing the index above to `3`. Lean rejects it because `3` is not a
valid element of `Fin 3`.
-/

/-! ## Multiset: mathlib-only note -/

/- 
The `Multiset` examples depend on mathlib. In a Lake project with mathlib,
this section can become a live demo.

Possible future demo:

  import Mathlib.Data.Multiset.Basic

  -- A multiset is unordered but keeps multiplicity.
  -- Compare `[1, 2, 1]` and `[1, 1, 2]` as multisets.
  -- Useful APIs include `card`, `count`, and `map`.

For the first lecture pass, keep the conceptual contrast:

  List      : finite ordered data
  Multiset  : finite unordered data with multiplicity
  Fin n     : a bounded natural number, useful for safe indexing
-/

/-!
Exercise ideas:
1. Use `Option` to handle a failed lookup.
2. Use `List.filter` and predict the result before evaluating it.
3. Construct an element of `Fin 5`.
4. Explain why `Fin` is useful for safe indexing.
-/

end D2CommonTypes
