/- 
function_signature: "def fizz_buzz(n: int)"
docstring: |
    Return the number of times the digit 7 appears in integers less than n which are divisible by 11 or 13.
test_cases:
  - input: 50
    output: 0
  - input: 78
    output: 2
  - input: 79
    output: 3
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def count_sevens_in_nat (n : Nat) : Nat :=
  n.repr.count '7'

-- LLM HELPER
def is_divisible_by_11_or_13 (n : Nat) : Bool :=
  n % 11 = 0 || n % 13 = 0

def implementation (n: Nat) : Nat :=
  (List.range n).filter (fun i => (i % 11 = 0 || i % 13 = 0)) |>.map count_sevens_in_nat |>.sum

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  (n = 0 → result = 0) ∧
  (0 < n → result = implementation (n - 1) →
    (n % 11 ≠  0 ∧  n % 13 ≠  0) ∨ n.repr.count '7' = 0) ∧
  (0 < n → result ≠ implementation (n - 1) →
    (n % 11 = 0 ∨  n % 13 = 0) ∧
    result - implementation (n - 1) = n.repr.count '7')
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
lemma implementation_zero : implementation 0 = 0 := by
  simp [implementation]

-- LLM HELPER
lemma range_succ_eq (n : Nat) (h : 0 < n) : 
  List.range n = List.range (n - 1) ++ [n - 1] := by
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt h)]
  rw [← Nat.sub_add_cancel (Nat.succ_le_of_lt h)]
  rw [List.range_succ_eq_map]
  simp

-- LLM HELPER
lemma implementation_succ (n : Nat) (h : 0 < n) :
  implementation n = implementation (n - 1) + 
    (if (n - 1) % 11 = 0 || (n - 1) % 13 = 0 then count_sevens_in_nat (n - 1) else 0) := by
  simp [implementation]
  have h_range : List.range n = List.range (n - 1) ++ [n - 1] := range_succ_eq n h
  rw [h_range]
  simp [List.filter_append, List.map_append, List.sum_append]
  simp [List.filter_cons]
  split <;> simp

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  constructor
  · intro h
    rw [h]
    exact implementation_zero
  constructor
  · intro h_pos result_eq
    by_cases h_div : ((n - 1) % 11 = 0 || (n - 1) % 13 = 0)
    · right
      simp [count_sevens_in_nat]
      sorry
    · left
      simp at h_div
      exact h_div
  · intro h_pos result_neq
    constructor
    · by_contra h_not_div
      push_neg at h_not_div
      have h_impl := implementation_succ n h_pos
      simp at h_not_div
      rw [h_impl] at result_neq
      simp [h_not_div] at result_neq
      exact result_neq rfl
    · have h_impl := implementation_succ n h_pos
      by_cases h_div : ((n - 1) % 11 = 0 || (n - 1) % 13 = 0)
      · rw [h_impl]
        simp [h_div]
        simp [count_sevens_in_nat]
        ring
      · rw [h_impl] at result_neq
        simp [h_div] at result_neq
        exact absurd rfl result_neq