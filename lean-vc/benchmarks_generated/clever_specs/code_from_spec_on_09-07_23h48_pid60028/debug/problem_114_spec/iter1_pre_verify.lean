def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(nums: List Int) :=
-- spec
let spec (result : Int) :=
  (∀ subarray ∈ nums.sublists,
    subarray.length > 0 →
    result ≤ subarray.sum) ∧
  (∃ subarray ∈ nums.sublists,
    subarray.length > 0 ∧
    result = subarray.sum)
-- program termination
∃ result,
  implementation nums = result ∧
  spec result

-- LLM HELPER
def min_subarray_sum_aux (nums: List Int) (current_min: Int) (current_sum: Int) : Int :=
  match nums with
  | [] => current_min
  | x :: xs => 
    let new_sum := min x (current_sum + x)
    let new_min := min current_min new_sum
    min_subarray_sum_aux xs new_min new_sum

def implementation (nums: List Int) : Int := 
  match nums with
  | [] => 0
  | x :: xs => min_subarray_sum_aux nums x 0

-- LLM HELPER
lemma sublists_nonempty_exists (nums: List Int) : nums ≠ [] → ∃ subarray ∈ nums.sublists, subarray.length > 0 := by
  intro h
  cases nums with
  | nil => contradiction
  | cons x xs =>
    use [x]
    constructor
    · simp [List.sublists]
      left
      simp [List.sublists']
      left
      simp
    · simp

-- LLM HELPER
lemma kadane_correctness_aux (nums: List Int) (current_min: Int) (current_sum: Int) :
  nums ≠ [] →
  (∀ subarray ∈ nums.sublists, subarray.length > 0 → current_min ≤ subarray.sum) →
  (∃ subarray ∈ nums.sublists, subarray.length > 0 ∧ current_min = subarray.sum) →
  let result := min_subarray_sum_aux nums current_min current_sum
  (∀ subarray ∈ nums.sublists, subarray.length > 0 → result ≤ subarray.sum) ∧
  (∃ subarray ∈ nums.sublists, subarray.length > 0 ∧ result = subarray.sum) := by
  intro h1 h2 h3
  induction nums generalizing current_min current_sum with
  | nil => contradiction
  | cons x xs ih =>
    simp [min_subarray_sum_aux]
    let new_sum := min x (current_sum + x)
    let new_min := min current_min new_sum
    by_cases h : xs = []
    · simp [h, min_subarray_sum_aux]
      constructor
      · intro subarray h_mem h_pos
        simp [List.sublists] at h_mem
        cases h_mem with
        | inl h_left =>
          simp [List.sublists'] at h_left
          cases h_left with
          | inl h_single =>
            simp at h_single
            rw [h_single]
            simp
            exact Int.min_le_right _ _
          | inr h_rest => simp [h] at h_rest
        | inr h_right => simp [h] at h_right
      · use [x]
        constructor
        · simp [List.sublists, List.sublists']
          left
          simp
        · simp
    · apply ih h
      · intro subarray h_mem h_pos
        have h_min_le : new_min ≤ current_min := Int.min_le_left _ _
        exact Int.le_trans h_min_le (h2 subarray h_mem h_pos)
      · cases h3 with
        | intro subarray h_exists =>
          cases h_exists with
          | intro h_mem h_eq =>
            use subarray
            constructor
            · exact h_mem
            · rw [← h_eq]
              exact Int.min_le_left _ _

-- LLM HELPER
lemma implementation_spec_empty : 
  let spec (result : Int) := 
    (∀ subarray ∈ ([] : List Int).sublists, subarray.length > 0 → result ≤ subarray.sum) ∧
    (∃ subarray ∈ ([] : List Int).sublists, subarray.length > 0 ∧ result = subarray.sum)
  spec 0 := by
  simp [List.sublists]
  constructor
  · intro subarray h_mem h_pos
    simp at h_mem
  · intro subarray h_mem h_pos
    simp at h_mem

-- LLM HELPER
lemma implementation_spec_nonempty (nums: List Int) :
  nums ≠ [] →
  let result := implementation nums
  let spec (result : Int) := 
    (∀ subarray ∈ nums.sublists, subarray.length > 0 → result ≤ subarray.sum) ∧
    (∃ subarray ∈ nums.sublists, subarray.length > 0 ∧ result = subarray.sum)
  spec result := by
  intro h
  cases nums with
  | nil => contradiction
  | cons x xs =>
    simp [implementation]
    apply kadane_correctness_aux
    · simp
    · intro subarray h_mem h_pos
      simp [List.sublists] at h_mem
      cases h_mem with
      | inl h_left =>
        simp [List.sublists'] at h_left
        cases h_left with
        | inl h_single =>
          simp at h_single
          rw [h_single]
          simp
          rfl
        | inr h_rest =>
          cases h_rest with
          | intro t h_t =>
            cases h_t with
            | intro h_t_mem h_t_eq =>
              rw [h_t_eq]
              simp
              exact Int.le_add_of_nonneg_right (Int.le_refl _)
      | inr h_right =>
        cases h_right with
        | intro s h_s =>
          cases h_s with
          | intro h_s_mem h_s_eq =>
            rw [h_s_eq]
            simp
            exact Int.le_add_of_nonneg_left (Int.le_refl _)
    · use [x]
      constructor
      · simp [List.sublists, List.sublists']
        left
        simp
      · simp

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  simp [problem_spec]
  use implementation nums
  constructor
  · rfl
  · by_cases h : nums = []
    · rw [h]
      exact implementation_spec_empty
    · exact implementation_spec_nonempty nums h