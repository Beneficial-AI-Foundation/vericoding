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
lemma grade_dict_length : grade_dict.length = 12 := by rfl

-- LLM HELPER
lemma find_grade_index_bounds (grade : Float) : 0 < grade → find_grade_index grade < 12 := by
  intro h
  unfold find_grade_index
  simp only [grade_dict_length]
  split_ifs <;> norm_num

-- LLM HELPER
lemma convert_grade_correct (grade : Float) : 0 < grade → 
  convert_grade grade = (grade_dict[find_grade_index grade]!).snd := by
  intro h
  unfold convert_grade find_grade_index grade_dict
  simp only [List.get_eq_getElem]
  split_ifs <;> simp

-- LLM HELPER
lemma grade_dict_sorted : ∀ i j, i < j → j < grade_dict.length → 
  (grade_dict[i]!).fst ≥ (grade_dict[j]!).fst := by
  intro i j hij hj
  unfold grade_dict
  simp only [List.get_eq_getElem]
  interval_cases i <;> interval_cases j <;> norm_num

-- LLM HELPER
lemma find_grade_index_correct (grade : Float) : 0 < grade → 
  (grade_dict[find_grade_index grade]!).fst ≤ grade ∧
  ∀ k, k < grade_dict.length → (grade_dict[k]!).fst ≤ grade → 
    (grade_dict[k]!).fst ≤ (grade_dict[find_grade_index grade]!).fst := by
  intro h
  constructor
  · unfold find_grade_index grade_dict
    simp only [List.get_eq_getElem]
    split_ifs <;> norm_num
  · intro k hk hkle
    have : find_grade_index grade < grade_dict.length := find_grade_index_bounds grade h
    unfold find_grade_index grade_dict at *
    simp only [List.get_eq_getElem] at *
    split_ifs at * <;> interval_cases k <;> norm_num

theorem correctness
(grades: List Float)
: problem_spec implementation grades
:= by
  unfold problem_spec implementation
  simp
  use grades.map convert_grade
  constructor
  · rfl
  · constructor
    · exact List.length_map grades convert_grade
    · intro i hi
      simp only [List.length_map] at hi
      simp [List.get_map]
      by_cases h1 : 0.0 < grades[i]!
      · simp [h1]
        let idx := find_grade_index grades[i]!
        use idx
        constructor
        · rw [grade_dict_length]
          exact find_grade_index_bounds grades[i]! h1
        · constructor
          · exact (find_grade_index_correct grades[i]! h1).1
          · constructor
            · exact (find_grade_index_correct grades[i]! h1).2
            · rw [convert_grade_correct grades[i]! h1]
      · simp [h1]
        have : grades[i]! ≤ 0.0 := by linarith
        rw [convert_grade]
        simp [this]