-- D6: Termination Proofs in Lean 4
-- Lean requires every function to terminate. Here we explore how.

-- Case 1: Structural recursion (Lean proves this automatically)
def list_len {A : Type} (xs : List A) : Nat :=
  match xs with
  | [] => 0
  | _ :: tail => 1 + list_len tail

#eval list_len [1, 2, 3, 4, 5]   -- 5

-- Case 2: Non-structural recursion requires a measure.
-- This version fails without termination_by:
-- def log2_bad (n : Nat) : Nat :=
--   if n < 2 then 0 else 1 + log2_bad (n / 2)

-- Fix: provide a termination measure.
-- Binding the condition (h : n < 2) adds it to the context,
-- so Lean can prove n / 2 < n in the else branch.
def log2 (n : Nat) : Nat :=
  if h : n < 2 then
    0
  else
    1 + log2 (n / 2)
termination_by n

#eval log2 1024   -- 10

-- Case 3: When automation fails, use decreasing_by.
-- The measure n decreases (n - k < n), but Lean can't prove
-- it automatically without knowing k >= 1 and n >= k.
def slow_div (n k : Nat) : Nat :=
  if h0 : k = 0 then 0
  else if h1 : n < k then 0
  else 1 + slow_div (n - k) k
termination_by n
decreasing_by
  -- h0 : ¬(k = 0)  means k ≥ 1
  -- h1 : ¬(n < k)  means n ≥ k
  -- Goal: n - k < n
  omega

#eval slow_div 17 5   -- 3  (= 17 / 5 rounded down)

-- Case 4: Measure can be a computed expression.
def process {A : Type} (arr : Array A) (i : Nat) : Nat :=
  if h : i < arr.size then
    1 + process arr (i + 1)
  else
    0
termination_by arr.size - i   -- i increases, but remaining work decreases
decreasing_by omega

#eval process #[10, 20, 30, 40] 0   -- 4

-- Case 5: Lexicographic measure (Ackermann function)
def ack (m n : Nat) : Nat :=
  match m, n with
  | 0, n => n + 1
  | m' + 1, 0 => ack m' 1
  | m' + 1, n' + 1 => ack m' (ack (m' + 1) n')
-- Lean automatically finds the lexicographic order (m, n)
termination_by (m, n)

#eval ack 3 4   -- 125
