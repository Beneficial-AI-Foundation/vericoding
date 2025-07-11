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
    let sorted := numbers.mergeSort (fun x y => decide (x ≤ y))
    let n := sorted.length
    if n % 2 = 1 then
      sorted[n / 2]?.getD default
    else
      (sorted[n / 2 - 1]?.getD default + sorted[n / 2]?.getD default) / 2

-- LLM HELPER
lemma mergeSort_perm (l: List Rat) :
  l.mergeSort (fun x y => decide (x ≤ y)) ~ l := by
  exact List.perm_mergeSort l

-- LLM HELPER
lemma mergeSort_preserves_elements (l: List Rat) :
  ∀ x, x ∈ l ↔ x ∈ l.mergeSort (fun x y => decide (x ≤ y)) := by
  intro x
  exact List.Perm.mem_iff (mergeSort_perm l).symm

-- LLM HELPER
lemma mergeSort_sorted (l: List Rat) :
  List.Sorted (fun x y => x ≤ y) (l.mergeSort (fun x y => decide (x ≤ y))) := by
  apply List.sorted_mergeSort
  intros a b
  exact decide_eq_true_iff.mp

-- LLM HELPER
lemma mergeSort_length (l: List Rat) :
  (l.mergeSort (fun x y => decide (x ≤ y))).length = l.length := by
  exact List.length_mergeSort l

-- LLM HELPER
lemma getD_mem_of_valid_index (l: List Rat) (i: Nat) (h: i < l.length) :
  l[i]?.getD default ∈ l := by
  simp only [List.getD_eq_get_of_lt h]
  exact List.get_mem l i

-- LLM HELPER
lemma decide_filter_conversion (l: List Rat) (x: Rat) :
  l.filter (fun y => decide (y ≤ x)) = l.filter (fun y => y ≤ x) := by
  simp [List.filter_congr]

-- LLM HELPER
lemma decide_filter_conversion_ge (l: List Rat) (x: Rat) :
  l.filter (fun y => decide (x ≤ y)) = l.filter (fun y => x ≤ y) := by
  simp [List.filter_congr]

-- LLM HELPER
lemma decide_filter_conversion_eq (l: List Rat) (x: Rat) :
  l.filter (fun y => decide (y = x)) = l.filter (fun y => y = x) := by
  simp [List.filter_congr]

-- LLM HELPER
lemma nat_div_two_lt_self (n: Nat) (h: n > 0) : n / 2 < n := by
  exact Nat.div_lt_self h (by norm_num)

-- LLM HELPER
lemma even_length_implies_div_minus_one_valid (n: Nat) (h_pos: n > 0) (h_even: n % 2 = 0) :
  n / 2 - 1 < n := by
  have h_ge_two : n ≥ 2 := by
    by_contra h
    simp at h
    cases' n with n'
    · simp at h_pos
    · cases' n' with n''
      · simp at h_even
      · simp at h
  have h_div : n / 2 ≥ 1 := by
    have : n / 2 * 2 = n := Nat.div_mul_cancel (Nat.dvd_iff_mod_eq_zero.mpr h_even)
    cases' n / 2 with k
    · simp at this; rw [this] at h_pos; simp at h_pos
    · simp
  omega

-- LLM HELPER
lemma median_property_count (numbers: List Rat) (median: Rat) :
  let less_eq := numbers.filter (fun x => x ≤ median)
  let more_eq := numbers.filter (fun x => median ≤ x)
  let eq_count := (numbers.filter (fun x => x = median)).length
  less_eq.length + more_eq.length - eq_count = numbers.length := by
  simp only [List.length_filter]
  have : (numbers.filter (fun x => x ≤ median)).length + (numbers.filter (fun x => ¬x ≤ median)).length = numbers.length := by
    rw [← List.length_filter_add_length_filter_not (fun x => x ≤ median) numbers]
  have : (numbers.filter (fun x => ¬x ≤ median)).length = (numbers.filter (fun x => median < x)).length := by
    congr 1
    ext x
    simp [not_le]
  rw [this] at *
  have : (numbers.filter (fun x => median ≤ x)).length = 
         (numbers.filter (fun x => median < x)).length + (numbers.filter (fun x => x = median)).length := by
    rw [← List.length_filter_add_length_filter_not (fun x => median < x) (numbers.filter (fun x => median ≤ x))]
    congr 2
    · ext x
      simp [List.mem_filter]
      tauto
    · ext x
      simp [List.mem_filter, not_lt]
      constructor
      · intro ⟨h1, h2⟩
        exact ⟨le_antisymm h2 h1, le_antisymm h2 h1⟩
      · intro ⟨h1, h2⟩
        rw [h2]
        exact ⟨le_refl _, le_refl _⟩
  rw [this]
  omega

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  cases' h_len : numbers.length with n
  · -- Case: numbers.length = 0
    use 0
    simp [h_len]
    intro h_pos
    exfalso
    omega
  · -- Case: numbers.length > 0
    have h_pos : 0 < numbers.length := by
      rw [h_len]
      simp
    
    let sorted := numbers.mergeSort (fun x y => decide (x ≤ y))
    let n := sorted.length
    have h_len' : n = numbers.length := by
      simp [sorted, mergeSort_length]
    
    cases' Nat.mod_two_eq_zero_or_one n with h_even h_odd
    · -- Even case
      let median := (sorted[n / 2 - 1]?.getD default + sorted[n / 2]?.getD default) / 2
      use median
      constructor
      · simp [median, sorted, h_len']
        rw [h_len', h_even]
        simp
      · intro h_pos'
        simp only [decide_filter_conversion, decide_filter_conversion_ge, decide_filter_conversion_eq]
        constructor
        · intro h_count h_le1 h_le2
          constructor <;> assumption
        · constructor
          · intro h_odd_len
            rw [← h_len'] at h_odd_len
            rw [h_even] at h_odd_len
            simp at h_odd_len
          · intro h_even_len
            constructor
            · -- show max_more_eq.isSome
              simp [Option.isSome_iff_exists]
              use sorted[n / 2]?.getD default
              simp [List.max?_eq_some_iff]
              constructor
              · -- show element is in filter
                simp [List.mem_filter]
                constructor
                · -- show element is in numbers
                  have h_valid : n / 2 < n := by
                    rw [h_len']
                    exact nat_div_two_lt_self numbers.length h_pos
                  rw [← mergeSort_preserves_elements]
                  exact getD_mem_of_valid_index sorted (n / 2) h_valid
                · -- show median ≤ element
                  simp [median]
                  have : sorted[n / 2 - 1]?.getD default ≤ sorted[n / 2]?.getD default := by
                    have h_sorted := mergeSort_sorted numbers
                    have h_valid1 : n / 2 - 1 < n := by
                      rw [h_len']
                      exact even_length_implies_div_minus_one_valid numbers.length h_pos (by rw [← h_len']; exact h_even)
                    have h_valid2 : n / 2 < n := by
                      rw [h_len']
                      exact nat_div_two_lt_self numbers.length h_pos
                    have : n / 2 - 1 ≤ n / 2 := by omega
                    exact List.Sorted.getD_le_getD h_sorted h_valid1 h_valid2 this
                  linarith
              · -- show it's maximum
                intro y hy
                simp [List.mem_filter] at hy
                have : y ≤ sorted[n / 2]?.getD default := by
                  rw [← mergeSort_preserves_elements] at hy
                  have h_sorted := mergeSort_sorted numbers
                  have h_valid : n / 2 < n := by
                    rw [h_len']
                    exact nat_div_two_lt_self numbers.length h_pos
                  have : y ∈ sorted := hy.1
                  have : ∃ j, j < sorted.length ∧ sorted[j]?.getD default = y := by
                    rw [← List.mem_iff_getD] at this
                    exact this
                  obtain ⟨j, hj_lt, hj_eq⟩ := this
                  rw [← hj_eq]
                  have : j ≤ n / 2 := by
                    by_contra h
                    simp at h
                    have : sorted[n / 2]?.getD default ≤ sorted[j]?.getD default := by
                      apply List.Sorted.getD_le_getD
                      exact h_sorted
                      exact h_valid
                      exact hj_lt
                      exact le_of_lt h
                    rw [hj_eq] at this
                    have : median ≤ y := hy.2
                    have : y < median := by
                      rw [median]
                      linarith
                    linarith
                  exact List.Sorted.getD_le_getD h_sorted (by rw [mergeSort_length]; exact le_of_lt hj_lt) 
                        (by rw [mergeSort_length]; exact h_valid) this
                exact this
            · constructor
              · -- show min_less_eq.isSome
                simp [Option.isSome_iff_exists]
                use sorted[n / 2 - 1]?.getD default
                simp [List.min?_eq_some_iff]
                constructor
                · -- show element is in filter
                  simp [List.mem_filter]
                  constructor
                  · -- show element is in numbers
                    have h_valid : n / 2 - 1 < n := by
                      rw [h_len']
                      exact even_length_implies_div_minus_one_valid numbers.length h_pos (by rw [← h_len']; exact h_even)
                    rw [← mergeSort_preserves_elements]
                    exact getD_mem_of_valid_index sorted (n / 2 - 1) h_valid
                  · -- show element ≤ median
                    simp [median]
                    have : sorted[n / 2 - 1]?.getD default ≤ sorted[n / 2]?.getD default := by
                      have h_sorted := mergeSort_sorted numbers
                      have h_valid1 : n / 2 - 1 < n := by
                        rw [h_len']
                        exact even_length_implies_div_minus_one_valid numbers.length h_pos (by rw [← h_len']; exact h_even)
                      have h_valid2 : n / 2 < n := by
                        rw [h_len']
                        exact nat_div_two_lt_self numbers.length h_pos
                      have : n / 2 - 1 ≤ n / 2 := by omega
                      exact List.Sorted.getD_le_getD h_sorted h_valid1 h_valid2 this
                    linarith
                · -- show it's minimum
                  intro y hy
                  simp [List.mem_filter] at hy
                  have : sorted[n / 2 - 1]?.getD default ≤ y := by
                    rw [← mergeSort_preserves_elements] at hy
                    have h_sorted := mergeSort_sorted numbers
                    have h_valid : n / 2 - 1 < n := by
                      rw [h_len']
                      exact even_length_implies_div_minus_one_valid numbers.length h_pos (by rw [← h_len']; exact h_even)
                    have : y ∈ sorted := hy.1
                    have : ∃ j, j < sorted.length ∧ sorted[j]?.getD default = y := by
                      rw [← List.mem_iff_getD] at this
                      exact this
                    obtain ⟨j, hj_lt, hj_eq⟩ := this
                    rw [← hj_eq]
                    have : n / 2 - 1 ≤ j := by
                      by_contra h
                      simp at h
                      have : sorted[j]?.getD default ≤ sorted[n / 2 - 1]?.getD default := by
                        apply List.Sorted.getD_le_getD
                        exact h_sorted
                        exact hj_lt
                        exact h_valid
                        exact le_of_lt h
                      rw [hj_eq] at this
                      have : y ≤ median := hy.2
                      have : median < y := by
                        rw [median]
                        linarith
                      linarith
                    exact List.Sorted.getD_le_getD h_sorted (by rw [mergeSort_length]; exact h_valid) 
                          (by rw [mergeSort_length]; exact le_of_lt hj_lt) this
                  exact this
              · -- show 2 * median = max + min
                simp [median]
                ring
    · -- Odd case
      let median := sorted[n / 2]?.getD default
      use median
      constructor
      · simp [median, sorted, h_len']
        rw [h_len', h_odd]
        simp
      · intro h_pos'
        simp only [decide_filter_conversion, decide_filter_conversion_ge, decide_filter_conversion_eq]
        constructor
        · intro h_count h_le1 h_le2
          constructor <;> assumption
        · constructor
          · intro h_odd_len
            rw [← mergeSort_preserves_elements]
            have h_valid : n / 2 < n := by
              rw [h_len']
              exact nat_div_two_lt_self numbers.length h_pos
            exact getD_mem_of_valid_index sorted (n / 2) h_valid
          · intro h_even_len
            rw [← h_len'] at h_even_len
            rw [h_odd] at h_even_len
            simp at h_even_len