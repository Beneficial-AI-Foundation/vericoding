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
def check_prefixes (operations: List Int) : Bool :=
  match operations with
  | [] => false
  | x :: xs => 
    if x < 0 then true
    else check_prefixes_helper xs x

-- LLM HELPER  
def check_prefixes_helper (operations: List Int) (acc: Int) : Bool :=
  match operations with
  | [] => false
  | x :: xs =>
    let new_acc := acc + x
    if new_acc < 0 then true
    else check_prefixes_helper xs new_acc

def implementation (operations: List Int) : Bool :=
  check_prefixes operations

-- LLM HELPER
lemma check_prefixes_correct (operations: List Int) :
  check_prefixes operations = true ↔ 
  ∃ i, i ≤ operations.length ∧ i > 0 ∧ (operations.take i).sum < 0 := by
  sorry

-- LLM HELPER
lemma empty_list_sum_nonneg : ∃ i, i ≤ ([] : List Int).length ∧ ([] : List Int).take i |>.sum < 0 ↔ False := by
  simp [List.length, List.take, List.sum]
  constructor
  · intro ⟨i, hi, _⟩
    simp at hi
    cases i with
    | zero => simp at *
    | succ n => simp at hi

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

theorem correctness
(operations: List Int)
: problem_spec implementation operations
:= by
  unfold problem_spec implementation
  use check_prefixes operations
  constructor
  · rfl
  · unfold check_prefixes
    cases operations with
    | nil => 
      simp [List.length, List.take, List.sum]
      constructor
      · intro ⟨i, _, h⟩
        cases i with
        | zero => simp at h
        | succ n => simp at h
    | cons x xs =>
      by_cases h : x < 0
      · simp [h]
        use 1
        simp [List.take, List.sum]
        exact h
      · simp [h]
        sorry

-- #test implementation [1, 2, 3] = false
-- #test implementation [1, 2, -4, 5] = true