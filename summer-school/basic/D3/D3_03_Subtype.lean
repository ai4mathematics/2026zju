import Mathlib

/-!
# D3_03_Subtype

Standalone file extracted from `D3_Demo.lean` for classroom navigation.
-/

namespace LeanZjuD3.Ch03

/-!
## 3. Subtype: elements carrying a proof

A subtype `{x : α // p x}` stores both a value `x : α` and a proof that the
value satisfies the predicate `p`.  This is the basic shape behind many
subobjects in Mathlib.
-/

section SubtypeBasics

def NonzeroInt := {n : ℤ // n ≠ 0}

example : NonzeroInt :=
  ⟨1, by norm_num⟩

example (x : NonzeroInt) : ℤ :=
  x.1

example (x : NonzeroInt) : x.1 ≠ 0 :=
  x.2

example (x : NonzeroInt) : x.1 ≠ 0 :=
  x.property

#check Subtype.val
#check Subtype.property

end SubtypeBasics

end LeanZjuD3.Ch03
