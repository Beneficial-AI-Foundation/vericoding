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

-- LLM HELPER
def check_prefixes_helper (operations: List Int) (acc: Int) : Bool :=
  match operations with
  | [] => false
  | x :: xs =>
    let new_acc := acc + x
    if new_acc < 0 then true
    else check_prefixes_helper xs new_acc

-- LLM HELPER
def check_prefixes (operations: List Int) : Bool :=
  match operations with
  | [] => false
  | x :: xs => 
    if x < 0 then true
    else check_prefixes_helper xs x

def implementation (operations: List Int) : Bool :=
  check_prefixes operations

-- LLM HELPER
lemma check_prefixes_helper_correct (operations: List Int) (acc: Int) :
  check_prefixes_helper operations acc = true ↔ 
  ∃ i, i ≤ operations.length ∧ i > 0 ∧ (List.take i operations).sum + acc < 0 := by
  induction operations generalizing acc with
  | nil => 
    simp [check_prefixes_helper]
    intro ⟨i, _, hi, _⟩
    cases i with
    | zero => simp at hi
    | succ n => simp
  | cons x xs ih =>
    simp [check_prefixes_helper]
    by_cases h : acc + x < 0
    · simp [h]
      use 1
      simp [List.take, List.sum, h]
    · simp [h]
      rw [ih]
      constructor
      · intro ⟨i, hi_le, hi_pos, hi_sum⟩
        use i + 1
        constructor
        · simp [List.length]
          omega
        · constructor
          · omega
          · simp [List.take, List.sum]
            rw [List.sum_cons]
            exact hi_sum
      · intro ⟨i, hi_le, hi_pos, hi_sum⟩
        cases i with
        | zero => simp at hi_pos
        | succ j =>
          use j
          constructor
          · simp [List.length] at hi_le
            omega
          · constructor
            · omega
            · simp [List.take, List.sum] at hi_sum
              rw [List.sum_cons] at hi_sum
              exact hi_sum

-- LLM HELPER
lemma check_prefixes_correct (operations: List Int) :
  check_prefixes operations = true ↔ 
  ∃ i, i ≤ operations.length ∧ i > 0 ∧ (operations.take i).sum < 0 := by
  cases operations with
  | nil => 
    simp [check_prefixes]
    intro ⟨i, _, hi, h⟩
    cases i with
    | zero => simp at hi
    | succ n => simp [List.take] at h
  | cons x xs =>
    simp [check_prefixes]
    by_cases h : x < 0
    · simp [h]
      use 1
      simp [List.take, List.sum]
      exact ⟨le_refl _, Nat.zero_lt_one, h⟩
    · simp [h]
      rw [check_prefixes_helper_correct]
      constructor
      · intro ⟨i, hi_le, hi_pos, hi_sum⟩
        use i + 1
        constructor
        · simp [List.length]
          omega
        · constructor
          · omega
          · simp [List.take, List.sum]
            rw [List.sum_cons]
            exact hi_sum
      · intro ⟨i, hi_le, hi_pos, hi_sum⟩
        cases i with
        | zero => simp at hi_pos
        | succ j =>
          use j
          constructor
          · simp [List.length] at hi_le
            omega
          · constructor
            · omega
            · simp [List.take, List.sum] at hi_sum
              rw [List.sum_cons] at hi_sum
              exact hi_sum

-- LLM HELPER
lemma empty_list_no_negative_prefix : 
  ¬∃ i, i ≤ ([] : List Int).length ∧ i > 0 ∧ ([] : List Int).take i |>.sum < 0 := by
  intro ⟨i, hi, hi_pos, h⟩
  simp [List.length] at hi
  cases i with
  | zero => simp at hi_pos
  | succ n => simp at hi

def problem_spec
-- function signature
(impl: List Int → Bool)
-- inputs
(operations: List Int) :=
-- spec
let below_zero_condition := ∃ i, i ≤ operations.length ∧ i > 0 ∧ (operations.take i).sum < 0
let spec (result: Bool) := if result then below_zero_condition else ¬below_zero_condition
-- program terminates
∃ result, impl operations = result ∧ spec result

theorem correctness
(operations: List Int)
: problem_spec implementation operations
:= by
  unfold problem_spec implementation
  use check_prefixes operations
  constructor
  · rfl
  · cases operations with
    | nil => 
      simp [check_prefixes]
      exact empty_list_no_negative_prefix
    | cons x xs =>
      rw [check_prefixes_correct]
      by_cases h : check_prefixes (x :: xs)
      · simp [h]
      · simp [h]

-- #test implementation [1, 2, 3] = false
-- #test implementation [1, 2, -4, 5] = true