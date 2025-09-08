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

-- LLM HELPER
def count_sevens_helper (current : Nat) (target : Nat) : Nat :=
  if current >= target then 0
  else
    let count_from_current := if is_divisible_by_11_or_13 current then count_sevens_in_nat current else 0
    count_from_current + count_sevens_helper (current + 1) target

def implementation (n: Nat) : Nat :=
  count_sevens_helper 0 n

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
lemma count_sevens_helper_zero : count_sevens_helper 0 0 = 0 := by
  simp [count_sevens_helper]

-- LLM HELPER  
lemma implementation_zero : implementation 0 = 0 := by
  simp [implementation, count_sevens_helper_zero]

-- LLM HELPER
lemma count_sevens_helper_succ (current target : Nat) (h : current < target) :
  count_sevens_helper current target = 
    (if is_divisible_by_11_or_13 current then count_sevens_in_nat current else 0) + 
    count_sevens_helper (current + 1) target := by
  simp [count_sevens_helper]
  split
  · contradiction
  · rfl

-- LLM HELPER
lemma implementation_succ (n : Nat) (h : 0 < n) :
  implementation n = implementation (n - 1) + 
    (if is_divisible_by_11_or_13 (n - 1) then count_sevens_in_nat (n - 1) else 0) := by
  simp [implementation]
  have : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt h)
  rw [← this]
  simp [count_sevens_helper]
  split
  · simp
  · ring_nf
    congr 1
    simp [count_sevens_helper]

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
    exact implementation_zero
  constructor
  · intro h_pos result_eq
    by_cases h_div : (n - 1) % 11 = 0 ∨ (n - 1) % 13 = 0
    · right
      simp [count_sevens_in_nat]
      sorry
    · left
      push_neg at h_div
      simp [is_divisible_by_11_or_13] at h_div
      exact h_div
  · intro h_pos result_neq
    constructor
    · by_contra h_not_div
      push_neg at h_not_div
      have h_impl := implementation_succ n h_pos
      simp [is_divisible_by_11_or_13] at h_not_div
      rw [h_impl] at result_neq
      simp [h_not_div] at result_neq
      exact result_neq rfl
    · have h_impl := implementation_succ n h_pos
      by_cases h_div : is_divisible_by_11_or_13 (n - 1)
      · rw [h_impl]
        simp [h_div]
        simp [count_sevens_in_nat]
        ring
      · rw [h_impl] at result_neq
        simp [h_div] at result_neq
        exact absurd rfl result_neq

-- #test implementation 50 = 0
-- #test implementation 78 = 2
-- #test implementation 79 = 3