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
def running_sums (operations: List Int) : List Int :=
  match operations with
  | [] => []
  | x :: xs => x :: (running_sums xs).map (· + x)

-- LLM HELPER
def has_negative_running_sum (operations: List Int) : Bool :=
  (running_sums operations).any (· < 0)

def implementation (operations: List Int) : Bool :=
  has_negative_running_sum operations

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
lemma running_sums_eq_take_sum (operations: List Int) (i: Nat) (h: i < (running_sums operations).length) :
  (running_sums operations).get ⟨i, h⟩ = (operations.take (i + 1)).sum := by
  induction operations generalizing i with
  | nil => simp [running_sums] at h
  | cons x xs ih =>
    cases i with
    | zero => 
      simp [running_sums, List.take, List.sum]
    | succ j =>
      have h': j < (running_sums xs).length := by
        simp [running_sums] at h
        cases running_sums xs with
        | nil => simp at h
        | cons _ _ => simp at h; exact Nat.lt_of_succ_lt_succ h
      rw [running_sums]
      simp only [List.get_cons_succ, List.map_get]
      rw [ih j h']
      simp only [List.take_succ_cons]
      ring

-- LLM HELPER  
lemma has_negative_running_sum_iff (operations: List Int) :
  has_negative_running_sum operations = true ↔ 
  ∃ i, i < operations.length ∧ (operations.take (i + 1)).sum < 0 := by
  simp [has_negative_running_sum, List.any_eq_true]
  constructor
  · intro ⟨x, hx_mem, hx_neg⟩
    obtain ⟨i, hi_bound, rfl⟩ := List.mem_iff_get.mp hx_mem
    use i
    constructor
    · cases operations with
      | nil => simp [running_sums] at hi_bound
      | cons y ys =>
        simp [running_sums] at hi_bound
        exact Nat.lt_of_lt_succ hi_bound
    · rw [running_sums_eq_take_sum operations i hi_bound]
      exact hx_neg
  · intro ⟨i, hi_bound, hi_neg⟩
    have hi_rs_bound : i < (running_sums operations).length := by
      cases operations with
      | nil => simp at hi_bound
      | cons x xs => 
        simp [running_sums]
        exact Nat.lt_succ_of_lt hi_bound
    use (running_sums operations).get ⟨i, hi_rs_bound⟩
    constructor
    · exact List.get_mem _ _
    · rw [running_sums_eq_take_sum operations i hi_rs_bound]
      exact hi_neg

theorem correctness
(operations: List Int)
: problem_spec implementation operations
:= by
  simp [problem_spec, implementation]
  use has_negative_running_sum operations
  constructor
  · rfl
  · by_cases h : has_negative_running_sum operations = true
    · simp [h]
      rw [has_negative_running_sum_iff] at h
      obtain ⟨i, hi_bound, hi_neg⟩ := h
      use i + 1
      constructor
      · exact Nat.succ_le_of_lt hi_bound
      · rw [List.take_succ_of_lt hi_bound]
        exact hi_neg
    · simp [h]
      intro i hi_bound
      rw [← has_negative_running_sum_iff] at h
      push_neg at h
      by_cases hi_zero : i = 0
      · simp [hi_zero, List.take, List.sum]
      · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
        have hi_pred : i - 1 < operations.length := by
          rw [Nat.sub_lt_iff_lt_add (Nat.one_le_of_lt hi_pos)]
          exact Nat.lt_of_succ_le hi_bound
        have hi_take : i = (i - 1) + 1 := Nat.succ_pred_eq_of_pos hi_pos
        rw [hi_take]
        by_contra h_neg
        have : has_negative_running_sum operations = true := by
          rw [has_negative_running_sum_iff]
          use i - 1
          exact ⟨hi_pred, h_neg⟩
        exact h this

-- #test implementation [1, 2, 3] = false
-- #test implementation [1, 2, -4, 5] = true