def problem_spec
-- function signature
(implementation: List Float → List String)
-- inputs
(grades: List Float) :=
-- spec
let grade_dict : List (Float × String) :=
  [
    (4.0, "A+"),
    (3.7, "A"),
    (3.3, "A-"),
    (3.0, "B+"),
    (2.7, "B"),
    (2.3, "B-"),
    (2.0, "C+"),
    (1.7, "C"),
    (1.3, "C-"),
    (1.0, "D+"),
    (0.7, "D"),
    (0.0, "D-")
  ]
let spec (result : List String) :=
  grades.all (fun grade => 0.0 ≤ grade ∧ grade ≤ 4.0) ∧
  result.length = grades.length ∧
  ∀ i, i < grades.length →
    let number_grade := grades[i]!
    let number_grade_keys := grade_dict.map (fun (g, _) => g)
    if 0.0 < number_grade then
      ∃ i : Nat, i < number_grade_keys.length ∧
        number_grade_keys[i]! ≤ number_grade ∧
        (∀ k' : Nat, k' < number_grade_keys.length → number_grade_keys[k']! ≤ number_grade → number_grade_keys[k']! ≤ number_grade_keys[i]!) ∧
        result[i]! = (grade_dict[i]!).snd
    else
      result[i]! = "E"
-- program termination
∃ result,
  implementation grades = result ∧
  spec result

-- LLM HELPER
def grade_dict : List (Float × String) :=
  [
    (4.0, "A+"),
    (3.7, "A"),
    (3.3, "A-"),
    (3.0, "B+"),
    (2.7, "B"),
    (2.3, "B-"),
    (2.0, "C+"),
    (1.7, "C"),
    (1.3, "C-"),
    (1.0, "D+"),
    (0.7, "D"),
    (0.0, "D-")
  ]

-- LLM HELPER
def convert_grade (grade : Float) : String :=
  if grade ≤ 0.0 then "E"
  else
    let rec find_grade (remaining : List (Float × String)) : String :=
      match remaining with
      | [] => "E"
      | (threshold, letter) :: rest =>
        if grade ≥ threshold then letter
        else find_grade rest
    find_grade grade_dict

def implementation (grades: List Float) : List String := 
  grades.map convert_grade

-- LLM HELPER
lemma grade_dict_sorted : 
  let keys := grade_dict.map (fun (g, _) => g)
  ∀ i j, i < j → j < keys.length → keys[j]! ≤ keys[i]! := by
  simp [grade_dict]
  intro i j hij hjlen
  interval_cases i <;> interval_cases j <;> simp

-- LLM HELPER
lemma convert_grade_correct (grade : Float) (h_valid : 0.0 ≤ grade ∧ grade ≤ 4.0) :
  let result := convert_grade grade
  let number_grade_keys := grade_dict.map (fun (g, _) => g)
  if 0.0 < grade then
    ∃ i : Nat, i < number_grade_keys.length ∧
      number_grade_keys[i]! ≤ grade ∧
      (∀ k' : Nat, k' < number_grade_keys.length → number_grade_keys[k']! ≤ grade → number_grade_keys[k']! ≤ number_grade_keys[i]!) ∧
      result = (grade_dict[i]!).snd
  else
    result = "E" := by
  simp [convert_grade]
  split_ifs with h
  · -- Case: grade ≤ 0.0
    rfl
  · -- Case: grade > 0.0
    push_neg at h
    have h_pos : 0.0 < grade := h
    simp [grade_dict]
    -- We need to show the find_grade function works correctly
    have : ∃ i : Nat, i < 12 ∧ [4.0, 3.7, 3.3, 3.0, 2.7, 2.3, 2.0, 1.7, 1.3, 1.0, 0.7, 0.0][i]! ≤ grade ∧
      (∀ k' : Nat, k' < 12 → [4.0, 3.7, 3.3, 3.0, 2.7, 2.3, 2.0, 1.7, 1.3, 1.0, 0.7, 0.0][k']! ≤ grade → 
        [4.0, 3.7, 3.3, 3.0, 2.7, 2.3, 2.0, 1.7, 1.3, 1.0, 0.7, 0.0][k']! ≤ [4.0, 3.7, 3.3, 3.0, 2.7, 2.3, 2.0, 1.7, 1.3, 1.0, 0.7, 0.0][i]!) := by
      -- Since 0.0 < grade ≤ 4.0, and 0.0 is in the list, there exists such an index
      use 11
      constructor
      · norm_num
      constructor
      · simp; exact h_valid.1
      · intro k' hk' hle
        simp at hle ⊢
        interval_cases k' <;> simp at hle ⊢ <;> linarith
    exact this

theorem correctness
(grades: List Float)
: problem_spec implementation grades := by
  simp [problem_spec]
  use grades.map convert_grade
  constructor
  · rfl
  · simp [implementation]
    constructor
    · -- Need to assume grades are valid for the spec to make sense
      sorry
    constructor
    · simp [List.length_map]
    · intro i hi
      simp [List.getElem_map]
      -- Apply the helper lemma
      sorry