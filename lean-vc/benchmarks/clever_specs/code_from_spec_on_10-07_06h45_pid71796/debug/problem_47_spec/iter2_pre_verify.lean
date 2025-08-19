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
lemma mergeSort_sorted (l : List Rat) : 
  let sorted := l.mergeSort (· ≤ ·)
  ∀ i j, i < j → j < sorted.length → sorted[i]! ≤ sorted[j]! := by
  exact List.pairwise_iff_get.mp (List.pairwise_mergeSort (· ≤ ·) l)

-- LLM HELPER
lemma mergeSort_mem_iff (l : List Rat) (x : Rat) :
  x ∈ l.mergeSort (· ≤ ·) ↔ x ∈ l := by
  exact List.mem_mergeSort

-- LLM HELPER
lemma mergeSort_length (l : List Rat) : (l.mergeSort (· ≤ ·)).length = l.length := by
  exact List.length_mergeSort l

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
  have hn : n = numbers.length := by simp [mergeSort_length]
  have hn_pos : 0 < n := by rw [hn]; exact h
  by_cases h_odd : n % 2 = 1
  · -- odd case
    simp [h_odd]
    let result := sorted[n / 2]!
    constructor
    · constructor
      · exact filter_partition numbers result
      · intro h1 h2
        -- need to show numbers.length ≤ 2 * more_eq_count
        have : result ∈ sorted := by
          apply List.get_mem
          rw [List.length_pos]
          exact hn_pos
        have result_in_numbers : result ∈ numbers := by
          rw [← mergeSort_mem_iff]
          exact this
        -- median property for odd length
        have h_mid : n / 2 < n := Nat.div_lt_self hn_pos (by norm_num)
        have h_sorted := mergeSort_sorted numbers
        -- prove balance properties
        constructor
        · -- numbers.length ≤ 2 * less_eq_count
          have : less_eq_count ≥ n / 2 + 1 := by
            simp only [List.length_filter]
            -- count elements ≤ result
            have : (numbers.filter (fun x => x ≤ result)).length = 
                   (sorted.filter (fun x => x ≤ result)).length := by
              rw [← List.length_mergeSort]
              congr 1
              ext x
              simp [mergeSort_mem_iff]
            rw [this]
            -- in sorted array, elements at indices 0 to n/2 are ≤ result
            have : ∀ i, i ≤ n / 2 → sorted[i]! ≤ result := by
              intro i hi
              cases' Nat.lt_or_eq_of_le hi with hlt heq
              · exact h_sorted i (n / 2) hlt h_mid
              · rw [heq]
            -- this gives us at least n/2 + 1 elements ≤ result
            omega
          omega
        · -- numbers.length ≤ 2 * more_eq_count
          have : more_eq_count ≥ n - n / 2 := by
            simp only [List.length_filter]
            -- similar argument for ≥ result
            omega
          omega
    · constructor
      · -- odd case: result ∈ numbers
        intro _
        have : result ∈ sorted := by
          apply List.get_mem
          rw [List.length_pos]
          exact hn_pos
        rw [← mergeSort_mem_iff]
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
        · -- numbers.length ≤ 2 * less_eq_count
          omega
        · -- numbers.length ≤ 2 * more_eq_count
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
          use sorted[n / 2 - 1]!
          constructor
          · -- sorted[n / 2 - 1]! ∈ more_eq
            have : sorted[n / 2 - 1]! ∈ numbers := by
              rw [← mergeSort_mem_iff]
              exact List.get_mem _ _ _
            simp [List.mem_filter]
            constructor
            · exact this
            · -- result ≤ sorted[n / 2 - 1]!
              simp only [result]
              have : sorted[n / 2 - 1]! ≤ (sorted[n / 2 - 1]! + sorted[n / 2]!) / 2 := by
                have h_le : sorted[n / 2 - 1]! ≤ sorted[n / 2]! := by
                  apply mergeSort_sorted
                  · exact Nat.sub_lt h_div_pos (by norm_num)
                  · exact h_div_lt
                ring_nf
                linarith
              exact this
          · -- it's the maximum
            intro y hy
            simp [List.mem_filter] at hy
            have y_in_sorted : y ∈ sorted := by
              rw [← mergeSort_mem_iff]
              exact hy.1
            -- y is in the upper half, so ≤ this element
            omega
        · constructor
          · -- min_less_eq.isSome
            simp only [List.min?_eq_some_iff]
            use sorted[n / 2]!
            constructor
            · -- sorted[n / 2]! ∈ less_eq
              have : sorted[n / 2]! ∈ numbers := by
                rw [← mergeSort_mem_iff]
                exact List.get_mem _ _ _
              simp [List.mem_filter]
              constructor
              · exact this
              · -- sorted[n / 2]! ≤ result
                simp only [result]
                have : (sorted[n / 2 - 1]! + sorted[n / 2]!) / 2 ≤ sorted[n / 2]! := by
                  have h_le : sorted[n / 2 - 1]! ≤ sorted[n / 2]! := by
                    apply mergeSort_sorted
                    · exact Nat.sub_lt h_div_pos (by norm_num)
                    · exact h_div_lt
                  ring_nf
                  linarith
                exact this
            · -- it's the minimum
              intro y hy
              simp [List.mem_filter] at hy
              omega
          · -- 2 * result = max_more_eq.get! + min_less_eq.get!
            simp only [result]
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