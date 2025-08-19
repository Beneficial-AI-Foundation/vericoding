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
  let max_more_eq := more_eq.maximum?;
  let min_less_eq := less_eq.minimum?;
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
def mergeSort (le : Rat → Rat → Bool) (l : List Rat) : List Rat :=
  if l.length ≤ 1 then l
  else
    let mid := l.length / 2
    let left := l.take mid
    let right := l.drop mid
    merge le (mergeSort le left) (mergeSort le right)
where
  merge le l1 l2 :=
    match l1, l2 with
    | [], l2 => l2
    | l1, [] => l1
    | h1::t1, h2::t2 =>
      if le h1 h2 then h1 :: merge le t1 l2
      else h2 :: merge le l1 t2
  termination_by l.length

-- LLM HELPER
def median_helper (numbers: List Rat) : Rat :=
  if numbers.length = 0 then 0 else
  let sorted := mergeSort (fun x y => decide (x ≤ y)) numbers
  let n := sorted.length
  if n % 2 = 1 then
    sorted.get! (n / 2)
  else
    (sorted.get! (n / 2 - 1) + sorted.get! (n / 2)) / 2

def implementation (numbers: List Rat) : Rat := median_helper numbers

-- LLM HELPER
lemma mergeSort_length (le : Rat → Rat → Bool) (l : List Rat) : 
  (mergeSort le l).length = l.length := by
  induction l using mergeSort.induct
  case case1 l h =>
    simp [mergeSort, h]
  case case2 l h =>
    simp [mergeSort, h]
    have h_merge : ∀ l1 l2, (mergeSort.merge le l1 l2).length = l1.length + l2.length := by
      intro l1 l2
      induction l1, l2 using mergeSort.merge.induct
      case case1 l2 => simp [mergeSort.merge]
      case case2 l1 => simp [mergeSort.merge]
      case case3 h1 t1 h2 t2 ih1 ih2 =>
        simp [mergeSort.merge]
        split_ifs with h_le
        · simp [ih1]
        · simp [ih2]
    rw [h_merge]
    simp [List.length_take, List.length_drop]
    omega

-- LLM HELPER
lemma mergeSort_mem (le : Rat → Rat → Bool) (l : List Rat) (x : Rat) :
  x ∈ mergeSort le l ↔ x ∈ l := by
  induction l using mergeSort.induct
  case case1 l h =>
    simp [mergeSort, h]
  case case2 l h =>
    simp [mergeSort, h]
    have h_merge : ∀ l1 l2, x ∈ mergeSort.merge le l1 l2 ↔ x ∈ l1 ∨ x ∈ l2 := by
      intro l1 l2
      induction l1, l2 using mergeSort.merge.induct
      case case1 l2 => simp [mergeSort.merge]
      case case2 l1 => simp [mergeSort.merge]
      case case3 h1 t1 h2 t2 ih1 ih2 =>
        simp [mergeSort.merge]
        split_ifs with h_le
        · simp [ih1]
        · simp [ih2]
    rw [h_merge]
    simp [List.mem_take, List.mem_drop]
    constructor
    · intro h_mem
      cases h_mem with
      | inl h_left => exact Or.inl ⟨h_left.1, h_left.2⟩
      | inr h_right => exact Or.inr (Nat.le_add_left _ _) h_right
    · intro h_mem
      cases h_mem with
      | inl h_left => exact Or.inl ⟨h_left.1, h_left.2⟩
      | inr h_right => exact Or.inr h_right

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
        omega
      · simp [h1, h2]
        omega
    · by_cases h2 : result ≤ x
      · simp [h1, h2]
        omega
      · simp [h1, h2]
        omega

-- LLM HELPER
lemma median_properties (numbers: List Rat) (h: 0 < numbers.length) :
  let result := median_helper numbers
  let less_eq := (numbers.filter (fun x => x ≤ result))
  let more_eq := (numbers.filter (fun x => result ≤ x))
  let max_more_eq := more_eq.maximum?
  let min_less_eq := less_eq.minimum?
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
  unfold median_helper
  simp [h]
  let sorted := mergeSort (fun x y => decide (x ≤ y)) numbers
  let n := sorted.length
  have hn : n = numbers.length := mergeSort_length (fun x y => decide (x ≤ y)) numbers
  have hn_pos : 0 < n := by rw [hn]; exact h
  constructor
  · constructor
    · exact filter_partition numbers (if n % 2 = 1 then sorted.get! (n / 2) else (sorted.get! (n / 2 - 1) + sorted.get! (n / 2)) / 2)
    · intro h1 h2
      constructor
      · exact h2
      · by_cases h_parity : n % 2 = 1
        · simp [h_parity]
          omega
        · simp [h_parity]
          omega
  · by_cases h_parity : n % 2 = 1
    · simp [h_parity]
      constructor
      · intro _
        have : sorted.get! (n / 2) ∈ sorted := by
          apply List.get!_mem
          rw [mergeSort_length]
          exact hn_pos
        rw [← mergeSort_mem]
        exact this
      · intro h_even
        have : n % 2 = 1 := h_parity
        rw [hn] at this
        contradiction
    · simp [h_parity]
      constructor
      · intro h_odd_contra
        have : n % 2 ≠ 1 := h_parity
        rw [hn] at this
        contradiction
      · intro h_even
        have hn_even : n % 2 = 0 := by
          rw [hn]
          exact h_even
        constructor
        · simp only [List.maximum?_eq_some_iff]
          use sorted.get! (n / 2)
          constructor
          · have : sorted.get! (n / 2) ∈ numbers := by
              rw [← mergeSort_mem]
              exact List.get!_mem _ _
            simp [List.mem_filter]
            constructor
            · exact this
            · omega
          · intro y hy
            omega
        · constructor
          · simp only [List.minimum?_eq_some_iff]
            use sorted.get! (n / 2 - 1)
            constructor
            · have : sorted.get! (n / 2 - 1) ∈ numbers := by
                rw [← mergeSort_mem]
                exact List.get!_mem _ _
              simp [List.mem_filter]
              constructor
              · exact this
              · omega
            · intro y hy
              omega
          · simp only [List.maximum?_eq_some_iff, List.minimum?_eq_some_iff]
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