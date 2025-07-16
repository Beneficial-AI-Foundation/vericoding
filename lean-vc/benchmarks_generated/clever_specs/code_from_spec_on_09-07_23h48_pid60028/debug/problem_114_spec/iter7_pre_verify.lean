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
  | x :: xs => min_subarray_sum_aux (x :: xs) x x

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
lemma single_element_sum (x : Int) : List.sum [x] = x := by
  simp [List.sum]

-- LLM HELPER
lemma empty_sum : List.sum ([] : List Int) = 0 := by
  simp [List.sum]

-- LLM HELPER
lemma empty_case_vacuous : ∀ subarray ∈ List.sublists ([] : List Int), subarray.length > 0 → False := by
  intro subarray h_mem h_pos
  simp [empty_list_only_empty_sublist] at h_mem
  rw [h_mem] at h_pos
  simp at h_pos

-- LLM HELPER
lemma single_element_works (x : Int) : 
  (∀ subarray ∈ List.sublists [x], subarray.length > 0 → x ≤ subarray.sum) ∧
  (∃ subarray ∈ List.sublists [x], subarray.length > 0 ∧ x = subarray.sum) := by
  constructor
  · intro subarray h_mem h_pos
    simp [single_element_sublists] at h_mem
    cases h_mem with
    | inl h => rw [h] at h_pos; simp at h_pos
    | inr h => rw [h]; simp [List.sum]
  · use [x]
    constructor
    · simp [single_element_sublists]
    · constructor
      · simp
      · simp [List.sum]

-- LLM HELPER
lemma kadane_invariant (nums : List Int) (current_min current_sum : Int) :
  min_subarray_sum_aux nums current_min current_sum = 
  min current_min (min_subarray_sum_aux nums current_sum current_sum) := by
  induction nums generalizing current_min current_sum with
  | nil => simp [min_subarray_sum_aux]
  | cons x xs ih =>
    simp [min_subarray_sum_aux]
    rw [ih]
    simp [min_assoc]

-- LLM HELPER
lemma min_subarray_sum_aux_achieves_minimum (nums : List Int) (current_min current_sum : Int) :
  ∃ subarray ∈ List.sublists nums, subarray.length > 0 ∧ 
  min_subarray_sum_aux nums current_min current_sum = min current_min subarray.sum := by
  induction nums generalizing current_min current_sum with
  | nil => 
    simp [min_subarray_sum_aux]
    exfalso
    exact empty_case_vacuous [] (by simp [empty_list_only_empty_sublist]) (by simp)
  | cons x xs ih =>
    simp [min_subarray_sum_aux]
    by_cases h : xs = []
    · rw [h]
      simp [min_subarray_sum_aux]
      use [x]
      constructor
      · simp [List.sublists]
        right
        use []
        simp [List.sublists]
      · constructor
        · simp
        · simp [min_def]
          split_ifs with h1 h2
          · rfl
          · simp [List.sum]
    · sorry

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  simp [problem_spec]
  use implementation nums
  constructor
  · rfl
  · by_cases h : nums = []
    · rw [h]
      simp [implementation]
      constructor
      · exact empty_case_vacuous
      · exfalso
        exact empty_case_vacuous [] (by simp [empty_list_only_empty_sublist]) (by simp)
    · cases nums with
      | nil => contradiction
      | cons x xs =>
        by_cases h_single : xs = []
        · rw [h_single]
          simp [implementation, min_subarray_sum_aux]
          exact single_element_works x
        · simp [implementation]
          constructor
          · intro subarray h_mem h_pos
            simp only [min_subarray_sum_aux]
            sorry
          · use [x]
            constructor
            · rw [mem_sublists_cons]
              right
              use []
              constructor
              · simp [List.sublists]
              · simp
            · constructor
              · simp
              · simp only [min_subarray_sum_aux, List.sum]
                sorry