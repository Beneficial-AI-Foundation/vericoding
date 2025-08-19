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
  else if grade ≥ 4.0 then "A+"
  else if grade ≥ 3.7 then "A"
  else if grade ≥ 3.3 then "A-"
  else if grade ≥ 3.0 then "B+"
  else if grade ≥ 2.7 then "B"
  else if grade ≥ 2.3 then "B-"
  else if grade ≥ 2.0 then "C+"
  else if grade ≥ 1.7 then "C"
  else if grade ≥ 1.3 then "C-"
  else if grade ≥ 1.0 then "D+"
  else if grade ≥ 0.7 then "D"
  else "D-"

def implementation (grades: List Float) : List String := 
  grades.map convert_grade

theorem correctness
(grades: List Float)
: problem_spec implementation grades
:= by
  unfold problem_spec implementation
  simp
  use grades.map convert_grade
  constructor
  · rfl
  · intro h
    constructor
    · exact List.length_map grades convert_grade
    · intro i hi
      simp [List.get_map]
      unfold convert_grade
      simp
      by_cases h1 : 0.0 < grades[i]!
      · simp [h1]
        by_cases h2 : grades[i]! ≥ 4.0
        · use 0
          simp [grade_dict, h2]
        · by_cases h3 : grades[i]! ≥ 3.7
          · use 1
            simp [grade_dict, h3, h2]
          · by_cases h4 : grades[i]! ≥ 3.3
            · use 2
              simp [grade_dict, h4, h3]
            · by_cases h5 : grades[i]! ≥ 3.0
              · use 3
                simp [grade_dict, h5, h4]
              · by_cases h6 : grades[i]! ≥ 2.7
                · use 4
                  simp [grade_dict, h6, h5]
                · by_cases h7 : grades[i]! ≥ 2.3
                  · use 5
                    simp [grade_dict, h7, h6]
                  · by_cases h8 : grades[i]! ≥ 2.0
                    · use 6
                      simp [grade_dict, h8, h7]
                    · by_cases h9 : grades[i]! ≥ 1.7
                      · use 7
                        simp [grade_dict, h9, h8]
                      · by_cases h10 : grades[i]! ≥ 1.3
                        · use 8
                          simp [grade_dict, h10, h9]
                        · by_cases h11 : grades[i]! ≥ 1.0
                          · use 9
                            simp [grade_dict, h11, h10]
                          · by_cases h12 : grades[i]! ≥ 0.7
                            · use 10
                              simp [grade_dict, h12, h11]
                            · use 11
                              simp [grade_dict, h12]
      · simp [h1]