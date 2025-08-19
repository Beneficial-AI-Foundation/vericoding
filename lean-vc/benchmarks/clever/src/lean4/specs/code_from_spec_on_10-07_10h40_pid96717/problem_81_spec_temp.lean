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

def implementation (grades: List Float) : List String := 
  grades.map grade_to_letter

theorem correctness
(grades: List Float)
: problem_spec implementation grades
:= by
  unfold problem_spec
  simp
  use grades.map grade_to_letter
  constructor
  · rfl
  · simp
    constructor
    · intro grade h
      cases' h with h1 h2
      constructor
      · assumption
      · assumption
    · constructor
      · simp [List.length_map]
      · intro i hi
        simp [List.get_map]
        sorry