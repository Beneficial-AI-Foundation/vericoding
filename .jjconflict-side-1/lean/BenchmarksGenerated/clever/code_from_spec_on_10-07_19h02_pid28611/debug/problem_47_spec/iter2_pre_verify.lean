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

def implementation (numbers: List Rat) : Rat :=
  if numbers.length = 0 then 0
  else
    let sorted := numbers.mergeSort (· ≤ ·)
    let n := sorted.length
    if n % 2 = 1 then
      sorted.get! (n / 2)
    else
      (sorted.get! (n / 2 - 1) + sorted.get! (n / 2)) / 2

-- LLM HELPER
lemma mergeSort_preserves_elements (l: List Rat) :
  ∀ x, x ∈ l ↔ x ∈ l.mergeSort (· ≤ ·) := by
  intro x
  exact List.mem_mergeSort

-- LLM HELPER
lemma mergeSort_sorted (l: List Rat) :
  (l.mergeSort (· ≤ ·)).Sorted (· ≤ ·) := by
  exact List.sorted_mergeSort

-- LLM HELPER
lemma mergeSort_length (l: List Rat) :
  (l.mergeSort (· ≤ ·)).length = l.length := by
  exact List.length_mergeSort

-- LLM HELPER
lemma get_mem_of_valid_index (l: List Rat) (i: Nat) :
  i < l.length → l.get! i ∈ l := by
  intro h
  exact List.getElem_mem l i h

-- LLM HELPER
lemma filter_le_length (l: List Rat) (p: Rat → Bool) :
  (l.filter p).length ≤ l.length := by
  exact List.length_filter_le l p

-- LLM HELPER
lemma filter_counts_property (l: List Rat) (x: Rat) :
  let less_eq := l.filter (fun y => y ≤ x)
  let more_eq := l.filter (fun y => x ≤ y)
  let eq_count := l.filter (fun y => y = x)
  less_eq.length + more_eq.length ≥ eq_count.length + l.length := by
  simp [List.length_filter_le]

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  split_ifs with h
  · -- Case: numbers.length = 0
    use 0
    simp [h]
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
        constructor
        · intro h_count h_le1 h_le2
          constructor <;> {
            have : (numbers.filter _).length ≤ numbers.length := filter_le_length _ _
            omega
          }
        · constructor
          · intro h_odd_len
            rw [← mergeSort_preserves_elements]
            apply get_mem_of_valid_index
            rw [mergeSort_length]
            have : n / 2 < n := by
              rw [h_len] at h_odd_len
              have : n > 0 := by rw [h_len]; exact h_pos
              exact Nat.div_lt_self this (by norm_num)
            rw [h_len]
            exact this
          · intro h_even
            have : numbers.length % 2 = 1 := by rw [← h_len]; exact h_odd
            simp [this] at h_even
    · -- Even case
      let median := (sorted.get! (n / 2 - 1) + sorted.get! (n / 2)) / 2
      use median
      constructor
      · simp [median, sorted, h_len]
      · intro h_pos'
        have h_even : numbers.length % 2 = 0 := by
          rw [← h_len]
          cases' Nat.mod_two_eq_zero_or_one n with h_mod h_mod
          · exact h_mod
          · simp [h_mod] at h_odd
        constructor
        · intro h_count h_le1 h_le2
          constructor <;> {
            have : (numbers.filter _).length ≤ numbers.length := filter_le_length _ _
            omega
          }
        · constructor
          · intro h_odd_len
            simp [h_even] at h_odd_len
          · intro h_even_len
            constructor
            · simp [List.max?_eq_none_iff]
              have : (numbers.filter (fun x => median ≤ x)).length > 0 := by
                have : sorted.get! (n / 2) ∈ sorted := by
                  apply get_mem_of_valid_index
                  have : n / 2 < n := by
                    have : n > 0 := by rw [h_len]; exact h_pos
                    exact Nat.div_lt_self this (by norm_num)
                  exact this
                rw [← mergeSort_preserves_elements] at this
                have : median ≤ sorted.get! (n / 2) := by
                  simp [median]
                  linarith
                have : sorted.get! (n / 2) ∈ numbers.filter (fun x => median ≤ x) := by
                  simp [List.mem_filter]
                  exact ⟨this, this⟩
                have : (numbers.filter (fun x => median ≤ x)).length > 0 := by
                  apply List.length_pos_of_mem
                  exact this
                exact this
              omega
            · constructor
              · simp [List.min?_eq_none_iff]
                have : (numbers.filter (fun x => x ≤ median)).length > 0 := by
                  have : sorted.get! (n / 2 - 1) ∈ sorted := by
                    apply get_mem_of_valid_index
                    have : n / 2 - 1 < n := by
                      have : n > 0 := by rw [h_len]; exact h_pos
                      have : n ≥ 2 := by
                        have : n % 2 = 0 := by rw [h_len]; exact h_even
                        cases' n with n'
                        · simp at h_pos h_len
                        · cases' n' with n''
                          · simp at this
                          · simp
                      omega
                    exact this
                  rw [← mergeSort_preserves_elements] at this
                  have : sorted.get! (n / 2 - 1) ≤ median := by
                    simp [median]
                    linarith
                  have : sorted.get! (n / 2 - 1) ∈ numbers.filter (fun x => x ≤ median) := by
                    simp [List.mem_filter]
                    exact ⟨this, this⟩
                  have : (numbers.filter (fun x => x ≤ median)).length > 0 := by
                    apply List.length_pos_of_mem
                    exact this
                  exact this
                omega
              · simp [median]
                ring