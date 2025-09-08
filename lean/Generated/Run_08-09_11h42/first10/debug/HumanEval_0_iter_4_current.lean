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
def check_pairs (numbers: List Rat) (threshold: Rat) (i: Nat) (j: Nat) : Bool :=
  if i < numbers.length ∧ j < numbers.length ∧ i ≠ j then
    |numbers[i]! - numbers[j]!| < threshold
  else
    false

-- LLM HELPER
def has_close_pair_aux (numbers: List Rat) (threshold: Rat) (i j: Nat) : Bool :=
  if i >= numbers.length then false
  else if j >= numbers.length then has_close_pair_aux numbers threshold (i + 1) 0
  else if i = j then has_close_pair_aux numbers threshold i (j + 1)
  else if |numbers[i]! - numbers[j]!| < threshold then true
  else has_close_pair_aux numbers threshold i (j + 1)

def implementation (numbers: List Rat) (threshold: Rat) : Bool :=
  has_close_pair_aux numbers threshold 0 0

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
-- if result then spec else ¬spec

-- LLM HELPER
lemma has_close_pair_aux_terminates (numbers: List Rat) (threshold: Rat) (i j: Nat) :
  ∃ result, has_close_pair_aux numbers threshold i j = result := by
  use has_close_pair_aux numbers threshold i j
  rfl

-- LLM HELPER
lemma exists_close_pair_iff (numbers: List Rat) (threshold: Rat) :
  has_close_pair_aux numbers threshold 0 0 = true ↔
  (∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧ |numbers[i]! - numbers[j]!| < threshold) := by
  constructor
  · intro h
    by_contra h_contra
    have h_false : has_close_pair_aux numbers threshold 0 0 = false := by
      have : ∀ i j, i < numbers.length → j < numbers.length → i ≠ j → |numbers[i]! - numbers[j]!| ≥ threshold := by
        intro i j hi hj hij
        by_contra h_close
        push_neg at h_close
        have : ∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧ |numbers[i]! - numbers[j]!| < threshold := 
          ⟨i, j, hi, hj, hij, h_close⟩
        exact h_contra this
      have aux_false : ∀ i j, has_close_pair_aux numbers threshold i j = false := by
        intro i j
        rw [has_close_pair_aux]
        by_cases hi : i >= numbers.length
        · simp [hi]
        · simp [hi]
          by_cases hj : j >= numbers.length
          · simp [hj]
            exact aux_false (i + 1) 0
          · simp [hj]
            by_cases hij : i = j
            · simp [hij]
              exact aux_false i (j + 1)
            · simp [hij]
              have hi_lt : i < numbers.length := Nat.lt_of_not_ge hi
              have hj_lt : j < numbers.length := Nat.lt_of_not_ge hj
              have close_ge : |numbers[i]! - numbers[j]!| ≥ threshold := this i j hi_lt hj_lt hij
              simp [not_lt.mpr close_ge]
              exact aux_false i (j + 1)
      exact aux_false 0 0
    rw [h_false] at h
    simp at h
  · intro h
    obtain ⟨i, j, hi, hj, hij, h_close⟩ := h
    have aux_true : ∀ k l, k ≤ i → l ≤ j → has_close_pair_aux numbers threshold k l = true := by
      intro k l hk hl
      have : ∃ m n, m ≥ k ∧ n ≥ l ∧ m < numbers.length ∧ n < numbers.length ∧ m ≠ n ∧ |numbers[m]! - numbers[n]!| < threshold := by
        use i, j
        exact ⟨Nat.le_trans hk (le_refl i), Nat.le_trans hl (le_refl j), hi, hj, hij, h_close⟩
      obtain ⟨m, n, hm_ge, hn_ge, hm_lt, hn_lt, hmn, h_close_mn⟩ := this
      rw [has_close_pair_aux]
      simp
      by_cases hk_ge : k >= numbers.length
      · have : k > i := Nat.lt_of_le_of_lt (Nat.le_of_lt_succ (Nat.lt_succ_iff.mpr hi)) hk_ge
        linarith [hk]
      · simp [hk_ge]
        exact True.intro
    exact aux_true 0 0 (Nat.zero_le i) (Nat.zero_le j)

theorem correctness
(numbers: List Rat)
(threshold: Rat)
: problem_spec implementation numbers threshold  := by
  unfold problem_spec implementation
  use has_close_pair_aux numbers threshold 0 0
  constructor
  · rfl
  · intro h
    by_cases h_result : has_close_pair_aux numbers threshold 0 0 = true
    · simp [h_result]
      rw [exists_close_pair_iff]
      exact h_result
    · simp [h_result]
      intro i hi j hj hij
      by_contra h_close
      push_neg at h_close
      have : ∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧ |numbers[i]! - numbers[j]!| < threshold := 
        ⟨i, j, hi, hj, hij, h_close⟩
      rw [exists_close_pair_iff] at this
      rw [this] at h_result
      simp at h_result

-- #test implementation ([1, 2, 3]: List Rat) 0.5 = false
-- #test implementation ([1, 2.8, 3, 4, 5, 2]: List Rat) 0.3 = true