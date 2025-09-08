/- 
function_signature: "def below_zero(operations: List[int]) -> bool"
docstring: |
    You're given a list of deposit and withdrawal operations on a bank account that starts with
    zero balance. Your task is to detect if at any point the balance of account fallls below zero, and
    at that point function should return True. Otherwise it should return False.
test_cases:
  - input:
      - 1
      - 2
      - 3
    expected_output: false
  - input:
      - 1
      - 2
      - -4
      - 5
    expected_output: true
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (operations: List Int) : Bool :=
  let rec check_prefixes (ops : List Int) (current_sum : Int) : Bool :=
    match ops with
    | [] => false
    | head :: tail => 
      let new_sum := current_sum + head
      if new_sum < 0 then true
      else check_prefixes tail new_sum
  check_prefixes operations 0

def problem_spec
-- function signature
(impl: List Int → Bool)
-- inputs
(operations: List Int) :=
-- spec
let below_zero_condition := ∃ i, i ≤ operations.length ∧
(operations.take i).sum < 0;
let spec (result: Bool) :=
if result then below_zero_condition else ¬below_zero_condition;
-- program terminates
∃ result, impl operations = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma sum_take_succ (l : List Int) (n : Nat) (h : n < l.length) :
  (l.take (n + 1)).sum = (l.take n).sum + l.get ⟨n, h⟩ := by
  rw [List.take_succ_get h]
  simp [List.sum_cons]

-- LLM HELPER
lemma check_prefixes_correct (ops : List Int) (start_sum : Int) :
  let rec check_prefixes (ops : List Int) (current_sum : Int) : Bool :=
    match ops with
    | [] => false
    | head :: tail => 
      let new_sum := current_sum + head
      if new_sum < 0 then true
      else check_prefixes tail new_sum
  check_prefixes ops start_sum = true ↔ 
  ∃ k, k < ops.length ∧ start_sum + (ops.take (k + 1)).sum < 0 := by
  induction ops generalizing start_sum with
  | nil => 
    simp [check_prefixes]
  | cons head tail ih =>
    simp only [check_prefixes]
    split
    · -- Case: start_sum + head < 0
      constructor
      · intro h
        use 0
        simp [List.take, List.sum]
        exact h
      · intro ⟨k, hk, hsum⟩
        cases k with
        | zero => 
          simp [List.take, List.sum] at hsum
          exact hsum
        | succ k' =>
          simp [List.take, List.sum] at hsum
          have : start_sum + head < 0 := by
            have : start_sum + head ≤ start_sum + head + (tail.take (k' + 1)).sum := by
              cases' le_or_gt 0 (tail.take (k' + 1)).sum with h h
              · exact le_add_of_nonneg_right h
              · linarith
            linarith
          assumption
    · -- Case: start_sum + head ≥ 0
      have h_ge : ¬(start_sum + head < 0) := by assumption
      rw [ih]
      constructor
      · intro ⟨k, hk, hsum⟩
        use k + 1
        constructor
        · simp; exact hk
        · simp [List.take]
          rw [List.sum_cons]
          exact hsum
      · intro ⟨k, hk, hsum⟩
        cases k with
        | zero =>
          simp [List.take, List.sum] at hsum
          contradiction
        | succ k' =>
          use k'
          constructor
          · simp at hk; exact hk
          · simp [List.take] at hsum
            rw [List.sum_cons] at hsum
            exact hsum

theorem correctness
(operations: List Int)
: problem_spec implementation operations
:= by
  unfold problem_spec implementation
  use implementation operations
  constructor
  · rfl
  · simp only [implementation]
    split_ifs with h
    · -- Case: implementation returns true
      unfold below_zero_condition
      rw [check_prefixes_correct]
      simp
      exact h
    · -- Case: implementation returns false
      unfold below_zero_condition
      push_neg
      intro i hi
      have : ¬(∃ k, k < operations.length ∧ 0 + (operations.take (k + 1)).sum < 0) := by
        rw [← check_prefixes_correct]
        simp
        exact h
      push_neg at this
      cases' le_or_gt i 0 with hi0 hi0
      · cases hi0 with
        | refl => simp [List.take, List.sum]
        | step => contradiction
      · cases' lt_or_eq_of_le hi with hi_lt hi_eq
        · have : i - 1 < operations.length := by omega
          have := this (i - 1) this
          simp at this
          convert this using 1
          rw [← Nat.succ_pred_eq_of_pos hi0]
          simp
        · rw [hi_eq]
          simp [List.take_length]
          have := this (operations.length - 1) (by omega)
          cases' eq_or_lt_of_le (Nat.zero_le operations.length) with h0 h0
          · simp [← h0]
          · have : operations.length - 1 + 1 = operations.length := Nat.succ_pred_eq_of_pos h0
            rw [← this] at hi_eq
            simp [this] at this
            exact le_of_not_gt this

-- #test implementation [1, 2, 3] = false
-- #test implementation [1, 2, -4, 5] = true