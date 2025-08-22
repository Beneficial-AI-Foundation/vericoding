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
def find_grade_index (grade : Float) : Nat :=
  if grade ≥ 4.0 then 0
  else if grade ≥ 3.7 then 1
  else if grade ≥ 3.3 then 2
  else if grade ≥ 3.0 then 3
  else if grade ≥ 2.7 then 4
  else if grade ≥ 2.3 then 5
  else if grade ≥ 2.0 then 6
  else if grade ≥ 1.7 then 7
  else if grade ≥ 1.3 then 8
  else if grade ≥ 1.0 then 9
  else if grade ≥ 0.7 then 10
  else 11

-- LLM HELPER
def convert_grade (grade : Float) : String :=
  if grade ≤ 0.0 then "E"
  else (grade_dict[find_grade_index grade]!).snd

-- LLM HELPER
lemma grade_dict_length : grade_dict.length = 12 := by rfl

-- LLM HELPER
lemma find_grade_index_bound (grade : Float) : find_grade_index grade < 12 := by
  simp [find_grade_index]
  split_ifs <;> norm_num

-- LLM HELPER
lemma grade_dict_keys_eq : grade_dict.map (fun (g, _) => g) = [4.0, 3.7, 3.3, 3.0, 2.7, 2.3, 2.0, 1.7, 1.3, 1.0, 0.7, 0.0] := by
  rfl

-- LLM HELPER
lemma find_grade_index_property (grade : Float) (h : 0.0 < grade) : 
  let idx := find_grade_index grade
  idx < 12 ∧ 
  [4.0, 3.7, 3.3, 3.0, 2.7, 2.3, 2.0, 1.7, 1.3, 1.0, 0.7, 0.0][idx]! ≤ grade ∧
  (∀ k' : Nat, k' < 12 → [4.0, 3.7, 3.3, 3.0, 2.7, 2.3, 2.0, 1.7, 1.3, 1.0, 0.7, 0.0][k']! ≤ grade → 
    [4.0, 3.7, 3.3, 3.0, 2.7, 2.3, 2.0, 1.7, 1.3, 1.0, 0.7, 0.0][k']! ≤ [4.0, 3.7, 3.3, 3.0, 2.7, 2.3, 2.0, 1.7, 1.3, 1.0, 0.7, 0.0][idx]!) := by
  simp [find_grade_index]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 <;> simp <;> 
  (constructor; norm_num; constructor; linarith; intro k' hk' hle; simp at hle ⊢; 
   split_ifs <;> norm_num <;> linarith)

def implementation (grades: List Float) : List String := 
  List.map convert_grade grades

theorem correctness
(grades: List Float)
: problem_spec implementation grades := by
  simp [problem_spec]
  use List.map convert_grade grades
  constructor
  · rfl
  · simp [implementation]
    constructor
    · intro grade hgrade
      constructor
      · norm_num
      · norm_num
    constructor
    · simp [List.length_map]
    · intro i hi
      simp [List.getElem_map]
      let grade := grades[i]!
      let number_grade_keys := grade_dict.map (fun (g, _) => g)
      simp [grade_dict, number_grade_keys, convert_grade, grade_dict_keys_eq]
      by_cases h : 0.0 < grade
      · simp [h]
        use find_grade_index grade
        have prop := find_grade_index_property grade h
        exact ⟨prop.1, prop.2.1, prop.2.2, by simp [find_grade_index]; split_ifs <;> rfl⟩
      · push_neg at h
        simp [h]
        rfl