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
lemma aux_implies_exists (numbers: List Rat) (threshold: Rat) (i j: Nat) :
  has_close_pair_aux numbers threshold i j = true →
  (∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧ |numbers[i]! - numbers[j]!| < threshold) := by
  intro h
  induction' numbers using List.length_induction with numbers ih generalizing i j
  unfold has_close_pair_aux at h
  by_cases hi : i >= numbers.length
  · simp [hi] at h
  · simp [hi] at h
    by_cases hj : j >= numbers.length
    · simp [hj] at h
      have : numbers.length < numbers.length + 1 := Nat.lt_succ_self _
      exact ih numbers (le_refl _) (i + 1) 0 h
    · simp [hj] at h
      by_cases hij : i = j
      · simp [hij] at h
        exact ih numbers (le_refl _) i (j + 1) h
      · simp [hij] at h
        by_cases close : |numbers[i]! - numbers[j]!| < threshold
        · simp [close] at h
          use i, j
          exact ⟨Nat.lt_of_not_ge hi, Nat.lt_of_not_ge hj, hij, close⟩
        · simp [close] at h
          exact ih numbers (le_refl _) i (j + 1) h

-- LLM HELPER
lemma exists_implies_aux (numbers: List Rat) (threshold: Rat) :
  (∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧ |numbers[i]! - numbers[j]!| < threshold) →
  has_close_pair_aux numbers threshold 0 0 = true := by
  intro ⟨i, j, hi, hj, hij, h_close⟩
  have aux_prop : ∀ k l, k ≤ numbers.length → l ≤ numbers.length → 
    (∃ m n, k ≤ m ∧ l ≤ n ∧ m < numbers.length ∧ n < numbers.length ∧ m ≠ n ∧ |numbers[m]! - numbers[n]!| < threshold) →
    has_close_pair_aux numbers threshold k l = true := by
    intro k l _ _ ⟨m, n, hkm, hln, hm, hn, hmn, h_close_mn⟩
    induction' numbers using List.length_induction with numbers ih generalizing k l m n
    unfold has_close_pair_aux
    by_cases hk : k >= numbers.length
    · have : k > m := by
        have : m < numbers.length := hm
        exact Nat.lt_of_le_of_lt hkm (Nat.lt_of_not_ge hk)
      linarith
    · simp [hk]
      by_cases hl : l >= numbers.length
      · simp [hl]
        apply ih numbers (le_refl _)
        use m, n
        exact ⟨Nat.le_trans (Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hk)) hkm, Nat.zero_le _, hm, hn, hmn, h_close_mn⟩
      · simp [hl]
        by_cases hkl : k = l
        · simp [hkl]
          apply ih numbers (le_refl _)
          use m, n
          exact ⟨hkm, Nat.le_trans (Nat.succ_le_succ (Nat.le_of_not_gt (not_lt.mpr (le_of_not_gt hl)))) hln, hm, hn, hmn, h_close_mn⟩
        · simp [hkl]
          by_cases close : |numbers[k]! - numbers[l]!| < threshold
          · simp [close]
          · simp [close]
            apply ih numbers (le_refl _)
            use m, n
            exact ⟨hkm, Nat.le_trans (Nat.succ_le_succ (Nat.le_of_not_gt (not_lt.mpr (le_of_not_gt hl)))) hln, hm, hn, hmn, h_close_mn⟩
  apply aux_prop 0 0 (Nat.zero_le _) (Nat.zero_le _)
  use i, j
  exact ⟨Nat.zero_le _, Nat.zero_le _, hi, hj, hij, h_close⟩

-- LLM HELPER
lemma exists_close_pair_iff (numbers: List Rat) (threshold: Rat) :
  has_close_pair_aux numbers threshold 0 0 = true ↔
  (∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧ |numbers[i]! - numbers[j]!| < threshold) := by
  constructor
  · exact aux_implies_exists numbers threshold 0 0
  · exact exists_implies_aux numbers threshold

-- LLM HELPER
lemma getD_eq_get (numbers : List Rat) (i : Nat) (hi : i < numbers.length) :
  numbers[i]?.getD default = numbers[i]! := by
  simp [List.getElem_getD, hi]

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
      intro i hi j hj hij h_close
      have h_close' : |numbers[i]! - numbers[j]!| < threshold := by
        rw [← getD_eq_get numbers i hi, ← getD_eq_get numbers j hj]
        exact h_close
      have : ∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧ |numbers[i]! - numbers[j]!| < threshold := 
        ⟨i, j, hi, hj, hij, h_close'⟩
      rw [← exists_close_pair_iff] at this
      rw [this] at h_result
      contradiction

-- #test implementation ([1, 2, 3]: List Rat) 0.5 = false
-- #test implementation ([1, 2.8, 3, 4, 5, 2]: List Rat) 0.3 = true