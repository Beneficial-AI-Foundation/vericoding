import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- LLM HELPER
-- Basic definitions and utility functions for grade conversion

def grade_to_letter (grade : Float) : String :=
  if grade ≤ 0.0 then "E"
  else if grade < 0.7 then "D-"
  else if grade < 1.0 then "D"
  else if grade < 1.3 then "D+"
  else if grade < 1.7 then "C-"
  else if grade < 2.0 then "C"
  else if grade < 2.3 then "C+"
  else if grade < 2.7 then "B-"
  else if grade < 3.0 then "B"
  else if grade < 3.3 then "B+"
  else if grade < 3.7 then "A-"
  else if grade < 4.0 then "A"
  else "A+"

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
      ∃ j : Nat, j < number_grade_keys.length ∧
        number_grade_keys[j]! ≤ number_grade ∧
        (∀ k' : Nat, k' < number_grade_keys.length → number_grade_keys[k']! ≤ number_grade → number_grade_keys[k']! ≤ number_grade_keys[j]!) ∧
        result[i]! = (grade_dict[j]!).snd
    else
      result[i]! = "E"
-- program termination
∃ result,
  implementation grades = result ∧
  spec result

def implementation (grades: List Float) : List String := 
  grades.map grade_to_letter

theorem correctness
(grades: List Float)
: problem_spec implementation grades
:= by
  unfold problem_spec implementation
  use grades.map grade_to_letter
  constructor
  · rfl
  constructor
  · intro grade hgrade
    constructor <;> simp
  constructor
  · simp [List.length_map]
  · intro i hi
    simp [List.get_map]
    by_cases h : 0.0 < grades[i]!
    · simp [h]
      let grade := grades[i]!
      if h1 : 4.0 ≤ grade then
        use 0
        constructor
        · norm_num
        constructor
        · simp; exact h1
        constructor
        · intro k hk _
          simp at hk
          interval_cases k <;> simp <;> linarith
        · unfold grade_to_letter
          simp [h1]
      else if h2 : 3.7 ≤ grade then
        use 1
        constructor
        · norm_num
        constructor
        · simp; exact h2
        constructor
        · intro k hk _
          simp at hk
          interval_cases k <;> simp <;> linarith
        · unfold grade_to_letter
          simp [h2, h1]
      else if h3 : 3.3 ≤ grade then
        use 2
        constructor
        · norm_num
        constructor
        · simp; exact h3
        constructor
        · intro k hk _
          simp at hk
          interval_cases k <;> simp <;> linarith
        · unfold grade_to_letter
          simp [h3, h2, h1]
      else if h4 : 3.0 ≤ grade then
        use 3
        constructor
        · norm_num
        constructor
        · simp; exact h4
        constructor
        · intro k hk _
          simp at hk
          interval_cases k <;> simp <;> linarith
        · unfold grade_to_letter
          simp [h4, h3, h2, h1]
      else if h5 : 2.7 ≤ grade then
        use 4
        constructor
        · norm_num
        constructor
        · simp; exact h5
        constructor
        · intro k hk _
          simp at hk
          interval_cases k <;> simp <;> linarith
        · unfold grade_to_letter
          simp [h5, h4, h3, h2, h1]
      else if h6 : 2.3 ≤ grade then
        use 5
        constructor
        · norm_num
        constructor
        · simp; exact h6
        constructor
        · intro k hk _
          simp at hk
          interval_cases k <;> simp <;> linarith
        · unfold grade_to_letter
          simp [h6, h5, h4, h3, h2, h1]
      else if h7 : 2.0 ≤ grade then
        use 6
        constructor
        · norm_num
        constructor
        · simp; exact h7
        constructor
        · intro k hk _
          simp at hk
          interval_cases k <;> simp <;> linarith
        · unfold grade_to_letter
          simp [h7, h6, h5, h4, h3, h2, h1]
      else if h8 : 1.7 ≤ grade then
        use 7
        constructor
        · norm_num
        constructor
        · simp; exact h8
        constructor
        · intro k hk _
          simp at hk
          interval_cases k <;> simp <;> linarith
        · unfold grade_to_letter
          simp [h8, h7, h6, h5, h4, h3, h2, h1]
      else if h9 : 1.3 ≤ grade then
        use 8
        constructor
        · norm_num
        constructor
        · simp; exact h9
        constructor
        · intro k hk _
          simp at hk
          interval_cases k <;> simp <;> linarith
        · unfold grade_to_letter
          simp [h9, h8, h7, h6, h5, h4, h3, h2, h1]
      else if h10 : 1.0 ≤ grade then
        use 9
        constructor
        · norm_num
        constructor
        · simp; exact h10
        constructor
        · intro k hk _
          simp at hk
          interval_cases k <;> simp <;> linarith
        · unfold grade_to_letter
          simp [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1]
      else if h11 : 0.7 ≤ grade then
        use 10
        constructor
        · norm_num
        constructor
        · simp; exact h11
        constructor
        · intro k hk _
          simp at hk
          interval_cases k <;> simp <;> linarith
        · unfold grade_to_letter
          simp [h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1]
      else
        use 11
        constructor
        · norm_num
        constructor
        · simp; linarith
        constructor
        · intro k hk _
          simp at hk
          interval_cases k <;> simp <;> linarith
        · unfold grade_to_letter
          simp [h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1]
    · simp [h]
      have : grades[i]! ≤ 0.0 := by linarith
      unfold grade_to_letter
      simp [this]