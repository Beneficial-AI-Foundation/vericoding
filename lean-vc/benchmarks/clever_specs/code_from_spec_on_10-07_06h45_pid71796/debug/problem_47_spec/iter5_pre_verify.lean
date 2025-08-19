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
def median_helper (numbers: List Rat) : Rat :=
  if numbers.length = 0 then 0 else
  let sorted := numbers.mergeSort (· ≤ ·)
  let n := sorted.length
  if n % 2 = 1 then
    sorted[n / 2]!
  else
    (sorted[n / 2 - 1]! + sorted[n / 2]!) / 2

def implementation (numbers: List Rat) : Rat := median_helper numbers

-- LLM HELPER
lemma filter_partition (numbers: List Rat) (result: Rat) :
  let less_eq := (numbers.filter (fun x => x ≤ result))
  let more_eq := (numbers.filter (fun x => result ≤ x))
  let eq_count := (numbers.filter (fun x => x = result)).length
  less_eq.length + more_eq.length - eq_count = numbers.length := by
  induction numbers with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons, List.length_cons]
    by_cases h1 : x ≤ result
    · by_cases h2 : result ≤ x
      · have h3 : x = result := le_antisymm h1 h2
        simp [h1, h2, h3]
        rw [← ih]
        omega
      · simp [h1, h2]
        rw [← ih]
        omega
    · by_cases h2 : result ≤ x
      · simp [h1, h2]
        rw [← ih]
        omega
      · simp [h1, h2]
        rw [← ih]
        omega

-- LLM HELPER
lemma median_properties (numbers: List Rat) (h: 0 < numbers.length) :
  let result := median_helper numbers
  let less_eq := (numbers.filter (fun x => x ≤ result))
  let more_eq := (numbers.filter (fun x => result ≤ x))
  let max_more_eq := more_eq.max?
  let min_less_eq := less_eq.min?
  let less_eq_count := less_eq.length
  let more_eq_count := more_eq.length
  let eq_count := (numbers.filter (fun x => x = result)).length
  (less_eq_count + more_eq_count - eq_count = numbers.length →
  numbers.length ≤ 2 * less_eq_count →
  numbers.length ≤ 2 * more_eq_count) ∧
  ((numbers.length % 2 = 1 →
    result ∈ numbers) ∧
    (numbers.length % 2 = 0 → max_more_eq.isSome ∧
    min_less_eq.isSome ∧
    2 * result = max_more_eq.get! + min_less_eq.get!)) := by
  simp only [median_helper]
  simp [h]
  let sorted := numbers.mergeSort (· ≤ ·)
  let n := sorted.length
  have hn : n = numbers.length := by simp [List.length_mergeSort]
  have hn_pos : 0 < n := by rw [hn]; exact h
  by_cases h_odd : n % 2 = 1
  · -- odd case
    simp [h_odd]
    let result := sorted[n / 2]!
    constructor
    · constructor
      · exact filter_partition numbers result
      · intro h1 h2
        constructor
        · exact h2
        · have : result ∈ sorted := by
            apply List.get_mem
            rw [List.length_pos]
            exact hn_pos
          have result_in_numbers : result ∈ numbers := by
            rw [← List.mem_mergeSort]
            exact this
          have h_mid : n / 2 < n := Nat.div_lt_self hn_pos (by norm_num)
          have h_sorted := List.pairwise_iff_get.mp (List.pairwise_mergeSort (· ≤ ·) numbers)
          have : more_eq_count ≥ n - n / 2 := by
            simp only [List.length_filter]
            have : (numbers.filter (fun x => result ≤ x)).length ≥ n - n / 2 := by
              have count_ge : (sorted.filter (fun x => result ≤ x)).length ≥ n - n / 2 := by
                have : ∀ i, n / 2 ≤ i → i < n → result ≤ sorted[i]! := by
                  intro i hi1 hi2
                  cases' Nat.lt_or_eq_of_le hi1 with hlt heq
                  · exact h_sorted (n / 2) i hlt hi2
                  · rw [← heq]
                simp [List.length_filter]
                have : (List.range n).filter (fun i => n / 2 ≤ i ∧ i < n) = List.range' (n / 2) (n - n / 2) := by
                  simp [List.range_eq_range']
                  ext i
                  simp [List.mem_range']
                  omega
                have card_ge : (List.range' (n / 2) (n - n / 2)).length = n - n / 2 := by
                  exact List.length_range' (n / 2) (n - n / 2)
                omega
              have : (numbers.filter (fun x => result ≤ x)).length = 
                     (sorted.filter (fun x => result ≤ x)).length := by
                rw [← List.length_mergeSort]
                congr 1
                ext x
                simp [List.mem_mergeSort]
              rw [this]
              exact count_ge
            exact this
          have : n ≤ 2 * (n - n / 2) := by
            have : n - n / 2 ≥ n / 2 := by
              have : n = (n / 2) + (n - n / 2) := by omega
              have : n % 2 = 1 := h_odd
              rw [hn] at this
              have : n = 2 * (n / 2) + 1 := Nat.div_add_mod n 2 ▸ this
              omega
            omega
          omega
    · constructor
      · -- odd case: result ∈ numbers
        intro _
        have : result ∈ sorted := by
          apply List.get_mem
          rw [List.length_pos]
          exact hn_pos
        rw [← List.mem_mergeSort]
        exact this
      · -- even case doesn't apply
        intro h_even
        have : n % 2 = 1 := h_odd
        rw [hn] at this
        contradiction
  · -- even case
    simp [h_odd]
    let result := (sorted[n / 2 - 1]! + sorted[n / 2]!) / 2
    constructor
    · constructor
      · exact filter_partition numbers result
      · intro h1 h2
        constructor
        · exact h2
        · have hn_even : n % 2 = 0 := by
            rw [hn]
            by_cases h : numbers.length % 2 = 0
            · exact h
            · have : numbers.length % 2 = 1 := by
                have : numbers.length % 2 < 2 := Nat.mod_two_lt_two numbers.length
                omega
              have : n % 2 = 1 := by rw [hn]; exact this
              contradiction
          have h_div_pos : 0 < n / 2 := by
            rw [Nat.div_pos_iff]
            constructor
            · exact hn_pos
            · norm_num
          have h_div_lt : n / 2 < n := Nat.div_lt_self hn_pos (by norm_num)
          have h_div_minus_lt : n / 2 - 1 < n := by
            have : n / 2 - 1 < n / 2 := Nat.sub_lt h_div_pos (by norm_num)
            exact Nat.lt_trans this h_div_lt
          have more_eq_count_ge : more_eq_count ≥ n / 2 := by
            simp only [List.length_filter]
            have : (numbers.filter (fun x => result ≤ x)).length ≥ n / 2 := by
              have : (sorted.filter (fun x => result ≤ x)).length ≥ n / 2 := by
                have : ∀ i, n / 2 ≤ i → i < n → result ≤ sorted[i]! := by
                  intro i hi1 hi2
                  simp only [result]
                  have h_sorted := List.pairwise_iff_get.mp (List.pairwise_mergeSort (· ≤ ·) numbers)
                  have h_le : sorted[n / 2 - 1]! ≤ sorted[i]! := by
                    apply h_sorted
                    · exact Nat.sub_lt h_div_pos (by norm_num)
                    · exact hi2
                  have : (sorted[n / 2 - 1]! + sorted[n / 2]!) / 2 ≤ sorted[i]! := by
                    have h_le2 : sorted[n / 2]! ≤ sorted[i]! := by
                      apply h_sorted
                      · exact h_div_lt
                      · exact hi2
                    have : sorted[n / 2 - 1]! ≤ sorted[n / 2]! := by
                      apply h_sorted
                      · exact Nat.sub_lt h_div_pos (by norm_num)
                      · exact h_div_lt
                    linarith
                  exact this
                omega
              have : (numbers.filter (fun x => result ≤ x)).length = 
                     (sorted.filter (fun x => result ≤ x)).length := by
                rw [← List.length_mergeSort]
                congr 1
                ext x
                simp [List.mem_mergeSort]
              rw [this]
              assumption
            exact this
          have : n ≤ 2 * n / 2 := by
            rw [← Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hn_even)]
          omega
    · constructor
      · -- odd case doesn't apply
        intro h_odd_contra
        have : n % 2 ≠ 1 := h_odd
        rw [hn] at this
        contradiction
      · -- even case
        intro h_even
        have hn_even : n % 2 = 0 := by
          rw [hn]
          exact h_even
        have h_div_pos : 0 < n / 2 := by
          rw [Nat.div_pos_iff]
          constructor
          · exact hn_pos
          · norm_num
        have h_div_lt : n / 2 < n := Nat.div_lt_self hn_pos (by norm_num)
        have h_div_minus_lt : n / 2 - 1 < n := by
          have : n / 2 - 1 < n / 2 := Nat.sub_lt h_div_pos (by norm_num)
          exact Nat.lt_trans this h_div_lt
        constructor
        · -- max_more_eq.isSome
          simp only [List.max?_eq_some_iff]
          use sorted[n / 2]!
          constructor
          · -- sorted[n / 2]! ∈ more_eq
            have : sorted[n / 2]! ∈ numbers := by
              rw [← List.mem_mergeSort]
              exact List.get_mem _ _ _
            simp [List.mem_filter]
            constructor
            · exact this
            · -- result ≤ sorted[n / 2]!
              simp only [result]
              have : sorted[n / 2 - 1]! ≤ sorted[n / 2]! := by
                apply List.pairwise_iff_get.mp (List.pairwise_mergeSort (· ≤ ·) numbers)
                · exact Nat.sub_lt h_div_pos (by norm_num)
                · exact h_div_lt
              linarith
          · -- it's the maximum
            intro y hy
            simp [List.mem_filter] at hy
            have y_in_sorted : y ∈ sorted := by
              rw [← List.mem_mergeSort]
              exact hy.1
            have : ∃ i, i < sorted.length ∧ sorted[i]! = y := by
              exact List.get_of_mem y_in_sorted
            obtain ⟨i, hi, hyi⟩ := this
            rw [← hyi]
            have : result ≤ sorted[i]! := hy.2
            rw [← hyi] at this
            simp only [result] at this
            have h_sorted := List.pairwise_iff_get.mp (List.pairwise_mergeSort (· ≤ ·) numbers)
            have : sorted[i]! ≤ sorted[n / 2]! := by
              by_cases h : i ≤ n / 2
              · exact h_sorted i (n / 2) (Nat.lt_of_le_of_ne h (fun h_eq => by
                  rw [h_eq] at this
                  have : sorted[n / 2 - 1]! ≤ sorted[n / 2]! := by
                    apply h_sorted
                    · exact Nat.sub_lt h_div_pos (by norm_num)
                    · exact h_div_lt
                  linarith)) h_div_lt
              · rfl
            exact this
        · constructor
          · -- min_less_eq.isSome
            simp only [List.min?_eq_some_iff]
            use sorted[n / 2 - 1]!
            constructor
            · -- sorted[n / 2 - 1]! ∈ less_eq
              have : sorted[n / 2 - 1]! ∈ numbers := by
                rw [← List.mem_mergeSort]
                exact List.get_mem _ _ _
              simp [List.mem_filter]
              constructor
              · exact this
              · -- sorted[n / 2 - 1]! ≤ result
                simp only [result]
                have : sorted[n / 2 - 1]! ≤ sorted[n / 2]! := by
                  apply List.pairwise_iff_get.mp (List.pairwise_mergeSort (· ≤ ·) numbers)
                  · exact Nat.sub_lt h_div_pos (by norm_num)
                  · exact h_div_lt
                linarith
            · -- it's the minimum
              intro y hy
              simp [List.mem_filter] at hy
              have y_in_sorted : y ∈ sorted := by
                rw [← List.mem_mergeSort]
                exact hy.1
              have : ∃ i, i < sorted.length ∧ sorted[i]! = y := by
                exact List.get_of_mem y_in_sorted
              obtain ⟨i, hi, hyi⟩ := this
              rw [← hyi]
              have : sorted[i]! ≤ result := hy.2
              rw [← hyi] at this
              simp only [result] at this
              have h_sorted := List.pairwise_iff_get.mp (List.pairwise_mergeSort (· ≤ ·) numbers)
              have : sorted[n / 2 - 1]! ≤ sorted[i]! := by
                by_cases h : n / 2 - 1 ≤ i
                · exact h_sorted (n / 2 - 1) i (Nat.lt_of_le_of_ne h (fun h_eq => by
                    rw [← h_eq] at this
                    have : sorted[n / 2 - 1]! ≤ sorted[n / 2]! := by
                      apply h_sorted
                      · exact Nat.sub_lt h_div_pos (by norm_num)
                      · exact h_div_lt
                    linarith)) hi
                · rfl
              exact this
          · -- 2 * result = max_more_eq.get! + min_less_eq.get!
            simp only [result]
            simp only [List.max?_eq_some_iff, List.min?_eq_some_iff]
            ring

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  use median_helper numbers
  constructor
  · rfl
  · intro h
    exact median_properties numbers h