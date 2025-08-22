import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Rat → Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: Rat) :=
  0 < numbers.length →
  let less_eq := (numbers.filter (fun x => x ≤ result));
  let more_eq := (numbers.filter (fun x => result ≤ x));
  let max_more_eq := more_eq.max?;
  let min_less_eq := less_eq.min?;
  let less_eq_count := less_eq.length;
  let more_eq_count := more_eq.length;
  let eq_count := (numbers.filter (fun x => x = result)).length;
  (less_eq_count + more_eq_count - eq_count = numbers.length →
  numbers.length ≤ 2 * less_eq_count →
  numbers.length ≤ 2 * more_eq_count) ∧
  ((numbers.length % 2 = 1 →
    result ∈ numbers) ∧
    (numbers.length % 2 = 0 → max_more_eq.isSome ∧
    min_less_eq.isSome ∧
    2 * result = max_more_eq.get! + min_less_eq.get!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def median_impl (numbers: List Rat) : Rat :=
  if numbers.length = 0 then 0
  else
    let sorted := numbers.mergeSort (· ≤ ·)
    let n := sorted.length
    if n % 2 = 1 then
      sorted.get! (n / 2)
    else
      (sorted.get! (n / 2 - 1) + sorted.get! (n / 2)) / 2

def implementation (numbers: List Rat) : Rat := median_impl numbers

-- LLM HELPER
lemma filter_le_median_of_sorted (sorted: List Rat) (median: Rat) :
  sorted.Sorted (· ≤ ·) →
  sorted.length > 0 →
  (sorted.length % 2 = 1 → median = sorted.get! (sorted.length / 2)) →
  (sorted.length % 2 = 0 → median = (sorted.get! (sorted.length / 2 - 1) + sorted.get! (sorted.length / 2)) / 2) →
  (sorted.filter (fun x => x ≤ median)).length ≥ sorted.length / 2 := by
  sorry

-- LLM HELPER
lemma filter_ge_median_of_sorted (sorted: List Rat) (median: Rat) :
  sorted.Sorted (· ≤ ·) →
  sorted.length > 0 →
  (sorted.length % 2 = 1 → median = sorted.get! (sorted.length / 2)) →
  (sorted.length % 2 = 0 → median = (sorted.get! (sorted.length / 2 - 1) + sorted.get! (sorted.length / 2)) / 2) →
  (sorted.filter (fun x => median ≤ x)).length ≥ sorted.length / 2 := by
  sorry

-- LLM HELPER
lemma median_in_list_odd (sorted: List Rat) :
  sorted.Sorted (· ≤ ·) →
  sorted.length > 0 →
  sorted.length % 2 = 1 →
  sorted.get! (sorted.length / 2) ∈ sorted := by
  apply List.getElem!_mem
  simp [List.length_pos_iff_ne_nil]
  sorry

-- LLM HELPER
lemma median_properties_even (sorted: List Rat) (median: Rat) :
  sorted.Sorted (· ≤ ·) →
  sorted.length > 0 →
  sorted.length % 2 = 0 →
  median = (sorted.get! (sorted.length / 2 - 1) + sorted.get! (sorted.length / 2)) / 2 →
  let less_eq := sorted.filter (fun x => x ≤ median)
  let more_eq := sorted.filter (fun x => median ≤ x)
  more_eq.max?.isSome ∧ less_eq.min?.isSome ∧
  2 * median = more_eq.max?.get! + less_eq.min?.get! := by
  sorry

-- LLM HELPER
lemma mergeSort_preserves_elements (l: List Rat) :
  ∀ x, x ∈ l ↔ x ∈ l.mergeSort (· ≤ ·) := by
  sorry

-- LLM HELPER
lemma mergeSort_sorted (l: List Rat) :
  (l.mergeSort (· ≤ ·)).Sorted (· ≤ ·) := by
  sorry

-- LLM HELPER
lemma mergeSort_length (l: List Rat) :
  (l.mergeSort (· ≤ ·)).length = l.length := by
  sorry

-- LLM HELPER
lemma filter_counts_add (l: List Rat) (x: Rat) :
  let less_eq := l.filter (fun y => y ≤ x)
  let more_eq := l.filter (fun y => x ≤ y)
  let eq_count := l.filter (fun y => y = x)
  less_eq.length + more_eq.length - eq_count.length = l.length := by
  sorry

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  unfold problem_spec implementation median_impl
  split_ifs with h
  · -- Case: numbers.length = 0
    simp [h]
    use 0
    simp
  · -- Case: numbers.length > 0
    have h_pos : 0 < numbers.length := by
      cases' numbers.length with n
      · simp at h
      · simp
    
    let sorted := numbers.mergeSort (· ≤ ·)
    let n := sorted.length
    have h_len : n = numbers.length := by
      simp [sorted, mergeSort_length]
    
    split_ifs with h_odd
    · -- Odd case
      let median := sorted.get! (n / 2)
      use median
      constructor
      · simp [median, sorted, h_len]
      · intro h_pos'
        simp [median, sorted, h_len, h_odd]
        constructor
        · intro h_count h_le1 h_le2
          constructor
          · apply filter_le_median_of_sorted
            · exact mergeSort_sorted numbers
            · rw [h_len]; exact h_pos
            · simp [h_odd]
            · simp [Nat.not_mod_two_eq_one_iff_mod_two_eq_zero.mp (by simp [h_odd])]
          · apply filter_ge_median_of_sorted
            · exact mergeSort_sorted numbers
            · rw [h_len]; exact h_pos
            · simp [h_odd]
            · simp [Nat.not_mod_two_eq_one_iff_mod_two_eq_zero.mp (by simp [h_odd])]
        · constructor
          · intro h_odd'
            rw [← mergeSort_preserves_elements]
            apply median_in_list_odd
            · exact mergeSort_sorted numbers
            · rw [h_len]; exact h_pos
            · rw [h_len]; exact h_odd'
          · intro h_even
            have : numbers.length % 2 = 1 := by rw [← h_len]; exact h_odd
            simp [this] at h_even
    · -- Even case
      let median := (sorted.get! (n / 2 - 1) + sorted.get! (n / 2)) / 2
      use median
      constructor
      · simp [median, sorted, h_len]
      · intro h_pos'
        simp [median, sorted, h_len]
        have h_even : numbers.length % 2 = 0 := by
          rw [← h_len]
          cases' Nat.mod_two_eq_zero_or_one n with h h
          · exact h
          · simp [h] at h_odd
        simp [h_even]
        constructor
        · intro h_count h_le1 h_le2
          constructor
          · apply filter_le_median_of_sorted
            · exact mergeSort_sorted numbers
            · rw [h_len]; exact h_pos
            · simp [h_even]
            · simp [h_even, median]
          · apply filter_ge_median_of_sorted
            · exact mergeSort_sorted numbers
            · rw [h_len]; exact h_pos
            · simp [h_even]
            · simp [h_even, median]
        · constructor
          · intro h_odd'
            simp [h_even] at h_odd'
          · intro h_even'
            rw [← mergeSort_preserves_elements] at *
            apply median_properties_even
            · exact mergeSort_sorted numbers
            · rw [h_len]; exact h_pos
            · rw [h_len]; exact h_even
            · simp [median]