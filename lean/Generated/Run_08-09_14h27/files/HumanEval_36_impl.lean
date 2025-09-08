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
lemma implementation_step (n : Nat) (h : 0 < n) : 
  implementation n = implementation (n - 1) + if (n - 1) % 11 = 0 ∨ (n - 1) % 13 = 0 then count_sevens_in_nat (n - 1) else 0 := by
  simp [implementation]
  have : List.range n = List.range (n - 1) ++ [n - 1] := by
    rw [← Nat.sub_add_cancel (Nat.succ_le_of_lt h)]
    simp [List.range_succ]
  rw [this]
  simp [List.filter_append, List.map_append, List.sum_append]
  simp [List.filter_cons, List.map_cons, List.sum_cons]
  split_ifs <;> simp

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
    -- When implementation n = implementation (n - 1)
    -- This means the (n-1)th element doesn't contribute
    have step := implementation_step n h_pos
    rw [result_eq] at step
    simp at step
    cases' h_div : ((n - 1) % 11 = 0 ∨ (n - 1) % 13 = 0) with
    | true =>
      -- If n-1 is divisible, then count_sevens_in_nat (n-1) must be 0
      simp [h_div] at step
      right
      simp [count_sevens_in_nat] at step
      exact step
    | false =>
      -- If n-1 is not divisible, then n-1 is not divisible by 11 or 13
      left
      simp at h_div
      -- Note: we need to show about n, not n-1
      -- But the spec seems to be asking about whether n contributes, not n-1
      -- Looking at the implementation, we check i from 0 to n-1
      -- So we should relate n-1's divisibility to the result
      cases' Nat.eq_zero_or_pos n with
      | inl h_zero => 
        rw [h_zero] at h_pos
        omega
      | inr h_pos_n =>
        -- The condition should be about whether adding element (n-1) changes the result
        -- Since result didn't change, either (n-1) is not divisible or has no 7s
        simp [h_div]
  · intro h_pos result_neq
    have step := implementation_step n h_pos
    simp at step
    constructor
    · -- Show (n-1) is divisible by 11 or 13 (since we're looking at range n, the last element is n-1)
      by_contra h_not_div
      simp at h_not_div
      rw [step] at result_neq
      simp [h_not_div] at result_neq
      simp at result_neq
    · -- Show the difference equals count of 7s in (n-1)
      have h_div : (n - 1) % 11 = 0 ∨ (n - 1) % 13 = 0 := by
        by_contra h
        simp at h
        rw [step] at result_neq
        simp [h] at result_neq
        simp at result_neq
      rw [step]
      simp [h_div]