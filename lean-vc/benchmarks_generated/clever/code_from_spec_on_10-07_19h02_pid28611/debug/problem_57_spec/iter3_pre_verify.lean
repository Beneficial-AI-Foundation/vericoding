import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → Bool)
-- inputs
(numbers: List Int) :=
let non_ordered := ∃ i j,
i < numbers.length - 1 ∧
j < numbers.length - 1 ∧
(numbers[i]! < numbers[i+1]!) ∧
(numbers[j+1]! < numbers[j]!);
-- spec
let spec (result: Bool) :=
  1 < numbers.length →
  result ↔ ¬non_ordered;
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def is_monotonic_increasing (numbers: List Int) : Bool :=
  numbers.zip (numbers.tail) |>.all (fun (a, b) => a ≤ b)

-- LLM HELPER
def is_monotonic_decreasing (numbers: List Int) : Bool :=
  numbers.zip (numbers.tail) |>.all (fun (a, b) => a ≥ b)

def implementation (numbers: List Int) : Bool := 
  is_monotonic_increasing numbers || is_monotonic_decreasing numbers

-- LLM HELPER
lemma non_ordered_iff_not_monotonic (numbers: List Int) :
  1 < numbers.length →
  ((is_monotonic_increasing numbers || is_monotonic_decreasing numbers) = true ↔
   ¬(∃ i j, i < numbers.length - 1 ∧ j < numbers.length - 1 ∧ 
    (numbers[i]! < numbers[i+1]!) ∧ (numbers[j+1]! < numbers[j]!))) := by
  intro h
  constructor
  · intro h_monotonic h_non_ordered
    obtain ⟨i, j, hi_lt, hj_lt, h_inc, h_dec⟩ := h_non_ordered
    cases' Bool.eq_true_iff_ne_false.mp h_monotonic with h_inc_true h_dec_true
    · unfold is_monotonic_increasing at h_inc_true
      simp [List.all_eq_true] at h_inc_true
      have h_i_in : (numbers[i]!, numbers[i+1]!) ∈ numbers.zip numbers.tail := by
        rw [List.mem_zip]
        constructor
        · exact Nat.lt_of_succ_lt_succ (Nat.succ_lt_succ hi_lt)
        · rw [List.length_tail]
          by_cases h_empty : numbers.length = 0
          · simp [h_empty] at h
          · simp [h_empty]
            exact hi_lt
      have h_le : numbers[i]! ≤ numbers[i+1]! := by
        have h_tail_eq : numbers.tail[i]! = numbers[i+1]! := by
          rw [List.get_tail]
        rw [← h_tail_eq]
        exact h_inc_true _ h_i_in
      exact not_le_of_lt h_inc h_le
    · unfold is_monotonic_decreasing at h_dec_true
      simp [List.all_eq_true] at h_dec_true
      have h_j_in : (numbers[j]!, numbers[j+1]!) ∈ numbers.zip numbers.tail := by
        rw [List.mem_zip]
        constructor
        · exact Nat.lt_of_succ_lt_succ (Nat.succ_lt_succ hj_lt)
        · rw [List.length_tail]
          by_cases h_empty : numbers.length = 0
          · simp [h_empty] at h
          · simp [h_empty]
            exact hj_lt
      have h_ge : numbers[j]! ≥ numbers[j+1]! := by
        have h_tail_eq : numbers.tail[j]! = numbers[j+1]! := by
          rw [List.get_tail]
        rw [← h_tail_eq]
        exact h_dec_true _ h_j_in
      exact not_le_of_lt h_dec h_ge
  · intro h_no_non_ordered
    by_contra h_not_monotonic
    simp [Bool.not_eq_true] at h_not_monotonic
    have h_not_inc : is_monotonic_increasing numbers = false := by
      simp [Bool.or_eq_false_iff] at h_not_monotonic
      exact h_not_monotonic.1
    have h_not_dec : is_monotonic_decreasing numbers = false := by
      simp [Bool.or_eq_false_iff] at h_not_monotonic
      exact h_not_monotonic.2
    unfold is_monotonic_increasing at h_not_inc
    unfold is_monotonic_decreasing at h_not_dec
    simp [List.all_eq_true, Bool.not_eq_true] at h_not_inc h_not_dec
    obtain ⟨i, hi_mem, hi_not⟩ := h_not_inc
    obtain ⟨j, hj_mem, hj_not⟩ := h_not_dec
    simp at hi_not hj_not
    have hi_lt : i < numbers.length - 1 := by
      rw [List.mem_zip] at hi_mem
      obtain ⟨hi_lt_len, hi_lt_tail⟩ := hi_mem
      rw [List.length_tail] at hi_lt_tail
      by_cases h_empty : numbers.length = 0
      · simp [h_empty] at h
      · simp [h_empty] at hi_lt_tail
        exact Nat.lt_sub_one_of_lt hi_lt_tail
    have hj_lt : j < numbers.length - 1 := by
      rw [List.mem_zip] at hj_mem
      obtain ⟨hj_lt_len, hj_lt_tail⟩ := hj_mem
      rw [List.length_tail] at hj_lt_tail
      by_cases h_empty : numbers.length = 0
      · simp [h_empty] at h
      · simp [h_empty] at hj_lt_tail
        exact Nat.lt_sub_one_of_lt hj_lt_tail
    have h_inc : numbers[i]! < numbers[i+1]! := by
      rw [List.mem_zip] at hi_mem
      have h_get : (numbers[i]!, numbers.tail[i]!) ∈ numbers.zip numbers.tail := hi_mem
      have h_tail_get : numbers.tail[i]! = numbers[i+1]! := by
        rw [List.get_tail]
      rw [← h_tail_get]
      exact Int.lt_of_not_le hi_not
    have h_dec : numbers[j+1]! < numbers[j]! := by
      rw [List.mem_zip] at hj_mem
      have h_get : (numbers[j]!, numbers.tail[j]!) ∈ numbers.zip numbers.tail := hj_mem
      have h_tail_get : numbers.tail[j]! = numbers[j+1]! := by
        rw [List.get_tail]
      rw [h_tail_get] at hj_not
      exact Int.lt_of_not_le hj_not
    exact h_no_non_ordered ⟨i, j, hi_lt, hj_lt, h_inc, h_dec⟩

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  simp only [exists_prop]
  use is_monotonic_increasing numbers || is_monotonic_decreasing numbers
  constructor
  · rfl
  · exact non_ordered_iff_not_monotonic numbers