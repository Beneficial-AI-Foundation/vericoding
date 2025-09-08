/- 
function_signature: "def has_close_elements(numbers: List[float], threshold: float) -> bool"
docstring: Check if in given list of numbers, are any two numbers closer to each other than given threshold.
test_cases:
  - input: [[1.0, 2.0, 3.0], 0.5]
    expected_output: False
  - input: [[1.0, 2.8, 3.0, 4.0, 5.0, 2.0], 0.3]
    expected_output: True
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER  
def check_all_pairs (numbers: List Rat) (threshold: Rat) : Bool :=
  match numbers with
  | [] => false
  | x :: xs => 
    (xs.any (fun y => |x - y| < threshold)) || check_all_pairs xs threshold

def implementation (numbers: List Rat) (threshold: Rat) : Bool :=
  check_all_pairs numbers threshold

def problem_spec
-- function signature
(impl: List Rat → Rat → Bool)
-- inputs
(numbers: List Rat)
(threshold: Rat) :=
-- spec
let numbers_within_threshold :=
(∃ i j, i < numbers.length ∧ j < numbers.length ∧
i ≠ j ∧ |numbers[i]! - numbers[j]!| < threshold);
let spec (res: Bool) :=
numbers.length > 1 →
if res then numbers_within_threshold else ¬numbers_within_threshold;
-- program terminates
∃ result, impl numbers threshold = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma check_all_pairs_correct (numbers: List Rat) (threshold: Rat) :
  check_all_pairs numbers threshold = true ↔ 
  ∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧ |numbers[i]! - numbers[j]!| < threshold := by
  induction numbers with
  | nil => 
    simp [check_all_pairs]
    constructor
    · intro h
      contradiction
    · intro ⟨i, j, hi, hj, _, _⟩
      simp at hi
  | cons x xs ih =>
    simp [check_all_pairs]
    constructor
    · intro h
      cases h with
      | inl h1 =>
        simp at h1
        obtain ⟨y, hy_mem, hy_close⟩ := h1
        obtain ⟨k, hk_eq⟩ := List.mem_iff_get.mp hy_mem
        use 0
        have hk_bound : k < xs.length := by
          rw [← List.length_pos_iff_exists_mem] at hy_mem
          exact k.isLt
        have hsucc_lt : k + 1 < (x :: xs).length := by
          simp
          exact Nat.succ_lt_succ hk_bound
        use k + 1, by simp, hsucc_lt
        simp
        constructor
        · rw [← hk_eq]
          exact hy_close
      | inr h2 =>
        obtain ⟨i, j, hi_lt, hj_lt, hi_ne_j, h_close⟩ := ih.mp h2
        have hi_succ_lt : i + 1 < (x :: xs).length := by
          simp
          exact hi_lt
        have hj_succ_lt : j + 1 < (x :: xs).length := by
          simp  
          exact hj_lt
        have hi_succ_bound : i < xs.length := hi_lt
        have hj_succ_bound : j < xs.length := hj_lt
        have hi_plus_one_bound : i + 1 < (x :: xs).length := by
          simp
          exact hi_lt
        use i + 1, j + 1, hi_plus_one_bound, by simp; exact hj_lt
        simp
        exact ⟨by simp [hi_ne_j], h_close⟩
    · intro ⟨i, j, hi_lt, hj_lt, hi_ne_j, h_close⟩
      cases' i with i'
      · cases' j with j'
        · contradiction
        · left
          simp
          have hj'_lt : j' < xs.length := Nat.lt_of_succ_lt_succ hj_lt
          use xs[j']!
          constructor
          · exact List.get_mem xs j' ⟨hj'_lt⟩
          · simp at h_close
            exact h_close
      · cases' j with j'
        · right
          apply ih.mpr
          use i', 0
          simp at hi_lt hj_lt h_close
          exact ⟨Nat.lt_of_succ_lt_succ hi_lt, hj_lt, by simp, h_close⟩
        · right
          apply ih.mpr
          use i', j'
          simp at hi_lt hj_lt hi_ne_j h_close
          exact ⟨Nat.lt_of_succ_lt_succ hi_lt, Nat.lt_of_succ_lt_succ hj_lt, 
                 fun h => hi_ne_j (by simp [h]), h_close⟩

theorem correctness
(numbers: List Rat)
(threshold: Rat)
: problem_spec implementation numbers threshold  := by
  simp [problem_spec, implementation]
  use check_all_pairs numbers threshold
  constructor
  · rfl
  · intro h_len
    by_cases h : check_all_pairs numbers threshold = true
    · simp [h]
      exact (check_all_pairs_correct numbers threshold).mp h
    · simp [h]
      intro contra
      have : check_all_pairs numbers threshold = true := 
        (check_all_pairs_correct numbers threshold).mpr contra
      contradiction

-- #test implementation ([1, 2, 3]: List Rat) 0.5 = false
-- #test implementation ([1, 2.8, 3, 4, 5, 2]: List Rat) 0.3 = true