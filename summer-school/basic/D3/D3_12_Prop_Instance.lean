import Mathlib

/-! Requires a configured Mathlib Lake project; see `README.md` in this folder. -/

/-!
# D3_12_Prop_Instance

Standalone file extracted from `D3_Demo.lean` for classroom navigation.
-/

namespace LeanZjuD3.Ch12

/-!
## 12. Proposition instances

Some typeclasses live in `Prop`.  They are not data structures with
computational content; they are automatically available proofs or properties.
-/

section PropositionInstances

instance : Fact (2 ≤ 5) := ⟨by norm_num⟩

example : 2 ≤ 5 := by
  exact Fact.out

example (n : Nat) [Fact (n ≠ 0)] : 0 < n := by
  exact Nat.pos_of_ne_zero (Fact.out : n ≠ 0)

class IsEven (n : Nat) : Prop where
  witness : ∃ k, n = 2 * k

instance : IsEven 8 where
  witness := ⟨4, by norm_num⟩

example [h : IsEven n] : ∃ k, n = 2 * k := by
  exact h.witness

example : ∃ k, 8 = 2 * k := by
  exact (inferInstance : IsEven 8).witness

end PropositionInstances

end LeanZjuD3.Ch12
