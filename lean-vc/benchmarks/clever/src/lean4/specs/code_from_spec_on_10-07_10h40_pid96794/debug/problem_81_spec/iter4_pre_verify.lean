import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
    constructor
    · simp [List.mem_map] at hgrade
      obtain ⟨g, _, rfl⟩ := hgrade
      simp
    · simp [List.mem_map] at hgrade
      obtain ⟨g, _, rfl⟩ := hgrade
      simp
  constructor
  · simp [List.length_map]
  · intro i hi
    simp [List.get_map]
    by_cases h : 0.0 < grades[i]!
    · simp [h]
      -- Find the correct j based on the grade value
      let grade := grades[i]!
      let keys := [4.0, 3.7, 3.3, 3.0, 2.7, 2.3, 2.0, 1.7, 1.3, 1.0, 0.7, 0.0]
      have keys_eq : keys = [(4.0, "A+"), (3.7, "A"), (3.3, "A-"), (3.0, "B+"), (2.7, "B"), (2.3, "B-"), (2.0, "C+"), (1.7, "C"), (1.3, "C-"), (1.0, "D+"), (0.7, "D"), (0.0, "D-")].map (fun (g, _) => g) := by rfl
      
      if h1 : 4.0 ≤ grade then
        use 0
        constructor
        · norm_num
        constructor
        · rw [keys_eq]; norm_num; exact h1
        constructor
        · intro k hk; rw [keys_eq]; norm_num at hk; norm_num; exact h1
        · unfold grade_to_letter
          simp only [List.get_eq_getElem]
          simp [h1]
          norm_num
      else if h2 : 3.7 ≤ grade then
        use 1
        constructor
        · norm_num
        constructor
        · rw [keys_eq]; norm_num; exact h2
        constructor
        · intro k hk; rw [keys_eq]; norm_num at hk; norm_num; 
          cases' hk with h h
          · rw [h]; norm_num; exact h1
          · exact h2
        · unfold grade_to_letter
          simp only [List.get_eq_getElem]
          simp [h2, h1]
          norm_num
      else if h3 : 3.3 ≤ grade then
        use 2
        constructor
        · norm_num
        constructor
        · rw [keys_eq]; norm_num; exact h3
        constructor
        · intro k hk; rw [keys_eq]; norm_num at hk; norm_num
          cases' hk with h h
          · rw [h]; norm_num; exact h1
          · cases' h with h h
            · rw [h]; norm_num; exact h2
            · exact h3
        · unfold grade_to_letter
          simp only [List.get_eq_getElem]
          simp [h3, h2, h1]
          norm_num
      else
        use 11
        constructor
        · norm_num
        constructor
        · rw [keys_eq]; norm_num; exact (le_of_lt h)
        constructor
        · intro k hk; rw [keys_eq]; norm_num at hk; norm_num; exact (le_of_lt h)
        · unfold grade_to_letter
          simp only [List.get_eq_getElem]
          simp [h3, h2, h1]
          norm_num
    · simp [h]
      have : grades[i]! ≤ 0.0 := by linarith
      simp [grade_to_letter]
      split_ifs with h1
      · rfl
      · linarith