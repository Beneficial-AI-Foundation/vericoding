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
      sorted.get! (n / 2)
    else
      (sorted.get! (n / 2 - 1) + sorted.get! (n / 2)) / 2

-- LLM HELPER
lemma mergeSort_preserves_elements (l: List Rat) :
  ∀ x, x ∈ l ↔ x ∈ l.mergeSort (fun x y => decide (x ≤ y)) := by
  intro x
  rw [List.mem_mergeSort]

-- LLM HELPER
lemma mergeSort_sorted (l: List Rat) :
  List.Sorted (fun x y => x ≤ y) (l.mergeSort (fun x y => decide (x ≤ y))) := by
  apply List.sorted_mergeSort
  intro a b
  simp only [decide_eq_true_iff]
  exact le_total a b

-- LLM HELPER
lemma mergeSort_length (l: List Rat) :
  (l.mergeSort (fun x y => decide (x ≤ y))).length = l.length := by
  exact List.length_mergeSort l

-- LLM HELPER
lemma get_mem_of_valid_index (l: List Rat) (i: Nat) (h: i < l.length) :
  l.get! i ∈ l := by
  exact List.getElem_mem l i

-- LLM HELPER
lemma filter_le_length (l: List Rat) (p: Rat → Bool) :
  (l.filter p).length ≤ l.length := by
  exact List.length_filter_le p l

-- LLM HELPER
lemma decide_filter_conversion (l: List Rat) (x: Rat) :
  l.filter (fun y => decide (y ≤ x)) = l.filter (fun y => y ≤ x) := by
  simp [List.filter_congr, decide_eq_true_iff]

-- LLM HELPER
lemma decide_filter_conversion_ge (l: List Rat) (x: Rat) :
  l.filter (fun y => decide (x ≤ y)) = l.filter (fun y => x ≤ y) := by
  simp [List.filter_congr, decide_eq_true_iff]

-- LLM HELPER
lemma decide_filter_conversion_eq (l: List Rat) (x: Rat) :
  l.filter (fun y => decide (y = x)) = l.filter (fun y => y = x) := by
  simp [List.filter_congr, decide_eq_true_iff]

-- LLM HELPER
lemma nat_div_two_lt_self (n: Nat) (h: n > 0) : n / 2 < n := by
  exact Nat.div_lt_self h (by norm_num)

-- LLM HELPER
lemma even_length_implies_div_minus_one_valid (n: Nat) (h_pos: n > 0) (h_even: n % 2 = 0) :
  n / 2 - 1 < n := by
  have h_ge_two : n ≥ 2 := by
    cases' n with n'
    · simp at h_pos
    · cases' n' with n''
      · simp at h_even
      · simp
  have h_div : n / 2 ≥ 1 := by
    have : n / 2 * 2 = n := Nat.div_mul_cancel (Nat.dvd_iff_mod_eq_zero.mpr h_even)
    cases' n / 2 with k
    · simp at this; rw [this] at h_pos; simp at h_pos
    · simp
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
      let median := (sorted.get! (n / 2 - 1) + sorted.get! (n / 2)) / 2
      use median
      constructor
      · simp [median, sorted, h_len']
        rw [h_len', h_even]
        simp
      · intro h_pos'
        simp [decide_filter_conversion, decide_filter_conversion_ge, decide_filter_conversion_eq]
        constructor
        · intro h_count h_le1 h_le2
          constructor <;> {
            have : (numbers.filter _).length ≤ numbers.length := filter_le_length _ _
            omega
          }
        · constructor
          · intro h_odd_len
            rw [← h_len'] at h_odd_len
            rw [h_even] at h_odd_len
            simp at h_odd_len
          · intro h_even_len
            constructor
            · simp [List.isSome_max?_iff]
              have : sorted.get! (n / 2) ∈ sorted := by
                apply get_mem_of_valid_index
                have : n / 2 < n := by
                  rw [h_len']
                  exact nat_div_two_lt_self numbers.length h_pos
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
              omega
            · constructor
              · simp [List.isSome_min?_iff]
                have : sorted.get! (n / 2 - 1) ∈ sorted := by
                  apply get_mem_of_valid_index
                  have : n / 2 - 1 < n := by
                    rw [h_len']
                    exact even_length_implies_div_minus_one_valid numbers.length h_pos (by rw [← h_len']; exact h_even)
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
                omega
              · simp [median]
                ring
    · -- Odd case
      let median := sorted.get! (n / 2)
      use median
      constructor
      · simp [median, sorted, h_len']
        rw [h_len', h_odd]
        simp
      · intro h_pos'
        simp [decide_filter_conversion, decide_filter_conversion_ge, decide_filter_conversion_eq]
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
              rw [h_len']
              exact nat_div_two_lt_self numbers.length h_pos
            rw [h_len']
            exact this
          · intro h_even_len
            rw [← h_len'] at h_even_len
            rw [h_odd] at h_even_len
            simp at h_even_len