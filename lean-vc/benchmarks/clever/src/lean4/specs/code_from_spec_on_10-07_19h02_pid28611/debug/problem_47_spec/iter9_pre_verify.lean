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

-- LLM HELPER
lemma mergeSort_length (l: List Rat) :
  (l.mergeSort (fun x y => decide (x ≤ y))).length = l.length := by
  exact List.length_mergeSort l

-- LLM HELPER
lemma get_mem_of_valid_index (l: List Rat) (i: Nat) (h: i < l.length) :
  l.get! i ∈ l := by
  have : l.get! i = l[i]! := by rfl
  rw [this]
  exact List.get!_mem l i h

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

-- LLM HELPER
lemma median_property_count (numbers: List Rat) (median: Rat) :
  let less_eq := numbers.filter (fun x => x ≤ median)
  let more_eq := numbers.filter (fun x => median ≤ x)
  let eq_count := (numbers.filter (fun x => x = median)).length
  less_eq.length + more_eq.length - eq_count = numbers.length := by
  simp only [List.length_filter]
  have h : ∀ x ∈ numbers, (x ≤ median ∧ median ≤ x) ↔ x = median := by
    intro x _
    constructor
    · intro ⟨h1, h2⟩
      exact le_antisymm h1 h2
    · intro h
      rw [h]
      exact ⟨le_refl _, le_refl _⟩
  rw [← List.length_filter_add_length_filter_not (fun x => x ≤ median) numbers]
  have : (numbers.filter (fun x => ¬x ≤ median)).length = (numbers.filter (fun x => median < x)).length := by
    congr 1
    ext x
    simp [not_le]
  rw [this]
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

-- LLM HELPER  
lemma median_balance_property (numbers: List Rat) (median: Rat) :
  let less_eq := numbers.filter (fun x => x ≤ median)
  let more_eq := numbers.filter (fun x => median ≤ x)
  less_eq.length ≥ numbers.length / 2 ∧ more_eq.length ≥ numbers.length / 2 →
  numbers.length ≤ 2 * less_eq.length ∧ numbers.length ≤ 2 * more_eq.length := by
  intro ⟨h1, h2⟩
  constructor
  · omega
  · omega

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
            · simp [List.isSome_max?_iff]
              have : (numbers.filter (fun x => median ≤ x)).length > 0 := by
                have h_valid : n / 2 < n := by
                  rw [h_len']
                  exact nat_div_two_lt_self numbers.length h_pos
                have : sorted.get! (n / 2) ∈ numbers := by
                  rw [← mergeSort_preserves_elements]
                  apply get_mem_of_valid_index
                  rw [mergeSort_length]
                  exact h_valid
                have : median ≤ sorted.get! (n / 2) := by
                  simp [median]
                  linarith
                have : sorted.get! (n / 2) ∈ numbers.filter (fun x => median ≤ x) := by
                  simp [List.mem_filter]
                  exact ⟨this, this⟩
                exact List.length_pos_of_mem _ this
              omega
            · constructor
              · simp [List.isSome_min?_iff]
                have : (numbers.filter (fun x => x ≤ median)).length > 0 := by
                  have h_valid : n / 2 - 1 < n := by
                    rw [h_len']
                    exact even_length_implies_div_minus_one_valid numbers.length h_pos (by rw [← h_len']; exact h_even)
                  have : sorted.get! (n / 2 - 1) ∈ numbers := by
                    rw [← mergeSort_preserves_elements]
                    apply get_mem_of_valid_index
                    rw [mergeSort_length]
                    exact h_valid
                  have : sorted.get! (n / 2 - 1) ≤ median := by
                    simp [median]
                    linarith
                  have : sorted.get! (n / 2 - 1) ∈ numbers.filter (fun x => x ≤ median) := by
                    simp [List.mem_filter]
                    exact ⟨this, this⟩
                  exact List.length_pos_of_mem _ this
                omega
              · have h_max : (numbers.filter (fun x => median ≤ x)).max? = some (sorted.get! (n / 2)) := by
                  have h_valid : n / 2 < n := by
                    rw [h_len']
                    exact nat_div_two_lt_self numbers.length h_pos
                  have h_mem : sorted.get! (n / 2) ∈ numbers := by
                    rw [← mergeSort_preserves_elements]
                    apply get_mem_of_valid_index
                    rw [mergeSort_length]
                    exact h_valid
                  have h_filter_mem : sorted.get! (n / 2) ∈ numbers.filter (fun x => median ≤ x) := by
                    simp [List.mem_filter, median]
                    exact ⟨h_mem, by linarith⟩
                  rw [List.max?_eq_some_iff]
                  exact ⟨h_filter_mem, fun y hy => by
                    simp [List.mem_filter] at hy
                    have : y ≤ sorted.get! (n / 2) := by
                      rw [← mergeSort_preserves_elements] at hy
                      have h_sorted := mergeSort_sorted numbers
                      have : y ∈ sorted := hy.1
                      have : ∃ j, j < sorted.length ∧ sorted.get! j = y := by
                        rw [← List.mem_iff_get!] at this
                        exact this
                      obtain ⟨j, hj_lt, hj_eq⟩ := this
                      rw [← hj_eq]
                      have : j ≤ n / 2 := by
                        by_contra h
                        simp at h
                        have : sorted.get! (n / 2) ≤ sorted.get! j := by
                          apply List.Sorted.get!_le_get!
                          exact h_sorted
                          rw [mergeSort_length]
                          exact h_valid
                          exact hj_lt
                          exact le_of_lt h
                        rw [hj_eq] at this
                        have : median ≤ y := hy.2
                        have : y < median := by
                          rw [median]
                          have : y ≤ sorted.get! (n / 2) := this
                          linarith
                        linarith
                      exact List.Sorted.get!_le_get! h_sorted (by rw [mergeSort_length]; exact le_of_lt hj_lt) 
                            (by rw [mergeSort_length]; exact h_valid) this⟩
                have h_min : (numbers.filter (fun x => x ≤ median)).min? = some (sorted.get! (n / 2 - 1)) := by
                  have h_valid : n / 2 - 1 < n := by
                    rw [h_len']
                    exact even_length_implies_div_minus_one_valid numbers.length h_pos (by rw [← h_len']; exact h_even)
                  have h_mem : sorted.get! (n / 2 - 1) ∈ numbers := by
                    rw [← mergeSort_preserves_elements]
                    apply get_mem_of_valid_index
                    rw [mergeSort_length]
                    exact h_valid
                  have h_filter_mem : sorted.get! (n / 2 - 1) ∈ numbers.filter (fun x => x ≤ median) := by
                    simp [List.mem_filter, median]
                    exact ⟨h_mem, by linarith⟩
                  rw [List.min?_eq_some_iff]
                  exact ⟨h_filter_mem, fun y hy => by
                    simp [List.mem_filter] at hy
                    have : sorted.get! (n / 2 - 1) ≤ y := by
                      rw [← mergeSort_preserves_elements] at hy
                      have h_sorted := mergeSort_sorted numbers
                      have : y ∈ sorted := hy.1
                      have : ∃ j, j < sorted.length ∧ sorted.get! j = y := by
                        rw [← List.mem_iff_get!] at this
                        exact this
                      obtain ⟨j, hj_lt, hj_eq⟩ := this
                      rw [← hj_eq]
                      have : n / 2 - 1 ≤ j := by
                        by_contra h
                        simp at h
                        have : sorted.get! j ≤ sorted.get! (n / 2 - 1) := by
                          apply List.Sorted.get!_le_get!
                          exact h_sorted
                          exact hj_lt
                          rw [mergeSort_length]
                          exact h_valid
                          exact le_of_lt h
                        rw [hj_eq] at this
                        have : y ≤ median := hy.2
                        have : median < y := by
                          rw [median]
                          have : sorted.get! (n / 2 - 1) ≤ y := this
                          linarith
                        linarith
                      exact List.Sorted.get!_le_get! h_sorted (by rw [mergeSort_length]; exact h_valid) 
                            (by rw [mergeSort_length]; exact le_of_lt hj_lt) this⟩
                rw [h_max, h_min]
                simp [median]
                ring
    · -- Odd case
      let median := sorted.get! (n / 2)
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