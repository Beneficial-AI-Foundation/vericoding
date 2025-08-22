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
def List.sublists (l : List α) : List (List α) :=
  match l with
  | [] => [[]]
  | a :: l => List.sublists l ++ (List.sublists l).map (fun x => a :: x)

-- LLM HELPER
def List.mysum (l : List Int) : Int :=
  match l with
  | [] => 0
  | a :: l => a + l.mysum

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
  | x :: xs => min_subarray_sum_aux (x :: xs) x 0

-- LLM HELPER
lemma sublists_cons (a : α) (l : List α) :
  List.sublists (a :: l) = List.sublists l ++ (List.sublists l).map (fun x => a :: x) := by
  simp [List.sublists]

-- LLM HELPER
lemma mem_sublists_cons (a : α) (l : List α) (s : List α) :
  s ∈ List.sublists (a :: l) ↔ s ∈ List.sublists l ∨ ∃ t ∈ List.sublists l, s = a :: t := by
  simp [sublists_cons]
  constructor
  · intro h
    exact h
  · intro h
    exact h

-- LLM HELPER
lemma empty_list_only_empty_sublist : List.sublists ([] : List α) = [[]] := by
  simp [List.sublists]

-- LLM HELPER
lemma single_element_sublists (x : α) : List.sublists [x] = [[], [x]] := by
  simp [List.sublists]

-- LLM HELPER
lemma single_element_sum (x : Int) : List.mysum [x] = x := by
  simp [List.mysum]

-- LLM HELPER
lemma empty_sum : List.mysum ([] : List Int) = 0 := by
  simp [List.mysum]

-- LLM HELPER
lemma min_subarray_sum_aux_le (nums: List Int) (current_min: Int) (current_sum: Int) :
  min_subarray_sum_aux nums current_min current_sum ≤ current_min := by
  induction nums generalizing current_min current_sum with
  | nil => simp [min_subarray_sum_aux]
  | cons x xs ih =>
    simp [min_subarray_sum_aux]
    apply ih
    
-- LLM HELPER
lemma implementation_achieves_bound (nums: List Int) : 
  nums ≠ [] → ∃ subarray ∈ List.sublists nums, subarray.length > 0 ∧ implementation nums = subarray.mysum := by
  intro h_nonempty
  cases nums with
  | nil => contradiction
  | cons x xs =>
    use [x]
    constructor
    · rw [mem_sublists_cons]
      right
      use []
      constructor
      · simp [List.sublists]
      · simp
    · constructor
      · simp
      · simp [implementation, single_element_sum]
        have : min_subarray_sum_aux (x :: xs) x 0 ≤ x := by
          apply min_subarray_sum_aux_le
        have : x ≤ min_subarray_sum_aux (x :: xs) x 0 := by
          cases xs with
          | nil => simp [min_subarray_sum_aux]
          | cons y ys => 
            simp [min_subarray_sum_aux]
            apply le_refl
        exact Int.eq_of_le_of_lt_succ this (Int.lt_succ_of_le this)

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  simp [problem_spec]
  use implementation nums
  constructor
  · rfl
  · by_cases h : nums = []
    · rw [h]
      simp [implementation, empty_list_only_empty_sublist, empty_sum]
      constructor
      · intro subarray h_mem h_pos
        simp at h_mem
        rw [h_mem] at h_pos
        simp at h_pos
      · intro subarray h_mem h_pos
        simp at h_mem
        rw [h_mem] at h_pos
        simp at h_pos
    · constructor
      · intro subarray h_mem h_pos
        cases nums with
        | nil => contradiction
        | cons x xs =>
          simp [implementation]
          have h_single : [x] ∈ List.sublists (x :: xs) := by
            rw [mem_sublists_cons]
            right
            use []
            constructor
            · simp [List.sublists]
            · simp
          have : min_subarray_sum_aux (x :: xs) x 0 ≤ x := by
            apply min_subarray_sum_aux_le
          have : x ≤ subarray.mysum := by
            have : subarray ∈ List.sublists (x :: xs) := h_mem
            have : subarray.length > 0 := h_pos
            cases subarray with
            | nil => simp at h_pos
            | cons y ys =>
              simp [List.mysum]
              have : y ≤ x := by
                have : [y] ∈ List.sublists (x :: xs) := by
                  rw [mem_sublists_cons]
                  right
                  use []
                  constructor
                  · simp [List.sublists]
                  · simp
                simp [List.mysum]
                exact le_refl _
              exact le_refl _
          exact le_trans this this
      · exact implementation_achieves_bound nums h