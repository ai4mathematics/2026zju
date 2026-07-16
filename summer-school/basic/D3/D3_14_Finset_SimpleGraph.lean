import Mathlib

/-! Requires a configured Mathlib Lake project; see `README.md` in this folder. -/

/-!
# D3_14_Finset_SimpleGraph

Standalone file extracted from `D3_Demo.lean` for classroom navigation.
-/

namespace LeanZjuD3.Ch14

/-!
## 14. Small combinatorics examples for `decide`, `simp`, and `ring`
-/

section FinsetAndGraph

open BigOperators
open Finset

#check Finset.range
#check Finset.card_range
#check Finset.filter
#check Finset.sum_range_succ

example : (Finset.range 5).card = 5 := by
  exact Finset.card_range 5

example : ((Finset.range 6).filter fun n => n % 2 = 0).card = 3 := by
  native_decide

example (n : Nat) : ∑ _i ∈ Finset.range (n + 1), (1 : Nat) = n + 1 := by
  simp

theorem sum_id (n : Nat) :
    ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) / 2 := by
  symm
  apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add 2, ← ih]
      ring

example : ∑ i ∈ Finset.range 5, i = 10 := by
  norm_num [sum_id]

def path3 : SimpleGraph (Fin 3) where
  Adj i j :=
    (i = 0 ∧ j = 1) ∨
    (i = 1 ∧ j = 0) ∨
    (i = 1 ∧ j = 2) ∨
    (i = 2 ∧ j = 1)
  symm := by
    unfold Symmetric
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  loopless := by
    constructor
    intro i h
    fin_cases i <;> simp_all

example : path3.Adj 0 1 := by
  simp [path3]

example : path3.Adj 1 2 := by
  simp [path3]

example : ¬ path3.Adj 0 2 := by
  simp [path3]

example (i : Fin 3) : ¬ path3.Adj i i := by
  fin_cases i <;> simp [path3]

example : (⊤ : SimpleGraph (Fin 3)).Adj 0 1 := by
  decide

example (i j : Fin 3) (h : path3.Adj i j) : i ≠ j := by
  exact SimpleGraph.ne_of_adj path3 h

example : path3.Adj 0 1 ∧ ¬ path3.Adj 0 2 := by
  constructor
  · simp [path3]
  · simp [path3]

example : (⊤ : SimpleGraph (Fin 4)).Adj 0 3 := by
  decide

end FinsetAndGraph

end LeanZjuD3.Ch14
