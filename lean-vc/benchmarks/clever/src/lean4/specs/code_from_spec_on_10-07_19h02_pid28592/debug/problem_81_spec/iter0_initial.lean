import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
  else if grade >= 4.0 then "A+"
  else if grade >= 3.7 then "A"
  else if grade >= 3.3 then "A-"
  else if grade >= 3.0 then "B+"
  else if grade >= 2.7 then "B"
  else if grade >= 2.3 then "B-"
  else if grade >= 2.0 then "C+"
  else if grade >= 1.7 then "C"
  else if grade >= 1.3 then "C-"
  else if grade >= 1.0 then "D+"
  else if grade >= 0.7 then "D"
  else "D-"

def implementation (grades: List Float) : List String := 
  grades.map convert_grade

-- LLM HELPER
lemma grade_dict_keys_eq : grade_dict.map (fun (g, _) => g) = [4.0, 3.7, 3.3, 3.0, 2.7, 2.3, 2.0, 1.7, 1.3, 1.0, 0.7, 0.0] := by
  simp [grade_dict]

-- LLM HELPER
lemma all_grades_valid : ∀ (grades : List Float), grades.all (fun grade => 0.0 ≤ grade ∧ grade ≤ 4.0) := by
  intro grades
  simp [List.all_eq_true]
  intro grade _
  constructor
  · exact Float.zero_le_abs grade
  · simp

-- LLM HELPER
lemma map_length (grades : List Float) : (grades.map convert_grade).length = grades.length := by
  exact List.length_map convert_grade grades

-- LLM HELPER
lemma convert_grade_correct (grade : Float) : 
  if 0.0 < grade then 
    ∃ i : Nat, i < grade_dict.length ∧ 
      (grade_dict[i]!).fst ≤ grade ∧
      (∀ k' : Nat, k' < grade_dict.length → (grade_dict[k']!).fst ≤ grade → (grade_dict[k']!).fst ≤ (grade_dict[i]!).fst) ∧
      convert_grade grade = (grade_dict[i]!).snd
  else 
    convert_grade grade = "E" := by
  simp [convert_grade, grade_dict]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  · simp at h1
    exact h1
  · use 0
    simp [grade_dict]
    constructor
    · norm_num
    constructor
    · exact h2
    constructor
    · intro k' hk' hle
      simp [grade_dict] at hk' hle
      interval_cases k' <;> simp [grade_dict] at hle <;> linarith
    · rfl
  · use 1
    simp [grade_dict]
    constructor
    · norm_num
    constructor
    · exact h3
    constructor
    · intro k' hk' hle
      simp [grade_dict] at hk' hle
      interval_cases k' <;> simp [grade_dict] at hle <;> linarith
    · rfl
  · use 2
    simp [grade_dict]
    constructor
    · norm_num
    constructor
    · exact h4
    constructor
    · intro k' hk' hle
      simp [grade_dict] at hk' hle
      interval_cases k' <;> simp [grade_dict] at hle <;> linarith
    · rfl
  · use 3
    simp [grade_dict]
    constructor
    · norm_num
    constructor
    · exact h5
    constructor
    · intro k' hk' hle
      simp [grade_dict] at hk' hle
      interval_cases k' <;> simp [grade_dict] at hle <;> linarith
    · rfl
  · use 4
    simp [grade_dict]
    constructor
    · norm_num
    constructor
    · exact h6
    constructor
    · intro k' hk' hle
      simp [grade_dict] at hk' hle
      interval_cases k' <;> simp [grade_dict] at hle <;> linarith
    · rfl
  · use 5
    simp [grade_dict]
    constructor
    · norm_num
    constructor
    · exact h7
    constructor
    · intro k' hk' hle
      simp [grade_dict] at hk' hle
      interval_cases k' <;> simp [grade_dict] at hle <;> linarith
    · rfl
  · use 6
    simp [grade_dict]
    constructor
    · norm_num
    constructor
    · exact h8
    constructor
    · intro k' hk' hle
      simp [grade_dict] at hk' hle
      interval_cases k' <;> simp [grade_dict] at hle <;> linarith
    · rfl
  · use 7
    simp [grade_dict]
    constructor
    · norm_num
    constructor
    · exact h9
    constructor
    · intro k' hk' hle
      simp [grade_dict] at hk' hle
      interval_cases k' <;> simp [grade_dict] at hle <;> linarith
    · rfl
  · use 8
    simp [grade_dict]
    constructor
    · norm_num
    constructor
    · exact h10
    constructor
    · intro k' hk' hle
      simp [grade_dict] at hk' hle
      interval_cases k' <;> simp [grade_dict] at hle <;> linarith
    · rfl
  · use 9
    simp [grade_dict]
    constructor
    · norm_num
    constructor
    · exact h11
    constructor
    · intro k' hk' hle
      simp [grade_dict] at hk' hle
      interval_cases k' <;> simp [grade_dict] at hle <;> linarith
    · rfl
  · use 10
    simp [grade_dict]
    constructor
    · norm_num
    constructor
    · exact h12
    constructor
    · intro k' hk' hle
      simp [grade_dict] at hk' hle
      interval_cases k' <;> simp [grade_dict] at hle <;> linarith
    · rfl
  · use 11
    simp [grade_dict]
    constructor
    · norm_num
    constructor
    · linarith
    constructor
    · intro k' hk' hle
      simp [grade_dict] at hk' hle
      interval_cases k' <;> simp [grade_dict] at hle <;> linarith
    · rfl
  · rfl

theorem correctness
(grades: List Float)
: problem_spec implementation grades
:= by
  simp [problem_spec, implementation]
  use grades.map convert_grade
  constructor
  · rfl
  constructor
  · exact all_grades_valid grades
  constructor
  · exact map_length grades
  · intro i hi
    simp [grade_dict_keys_eq]
    exact convert_grade_correct (grades[i]!)