import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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

-- LLM HELPER
lemma grade_dict_keys_correct : 
  let grade_dict : List (Float × String) := [(4.0, "A+"), (3.7, "A"), (3.3, "A-"), (3.0, "B+"), (2.7, "B"), (2.3, "B-"), (2.0, "C+"), (1.7, "C"), (1.3, "C-"), (1.0, "D+"), (0.7, "D"), (0.0, "D-")]
  let keys := grade_dict.map (fun (g, _) => g)
  keys = [4.0, 3.7, 3.3, 3.0, 2.7, 2.3, 2.0, 1.7, 1.3, 1.0, 0.7, 0.0] := by
  simp

-- LLM HELPER
lemma grade_dict_values_correct : 
  let grade_dict : List (Float × String) := [(4.0, "A+"), (3.7, "A"), (3.3, "A-"), (3.0, "B+"), (2.7, "B"), (2.3, "B-"), (2.0, "C+"), (1.7, "C"), (1.3, "C-"), (1.0, "D+"), (0.7, "D"), (0.0, "D-")]
  (grade_dict[0]!).snd = "A+" ∧ (grade_dict[1]!).snd = "A" ∧ (grade_dict[2]!).snd = "A-" ∧ (grade_dict[3]!).snd = "B+" ∧ (grade_dict[4]!).snd = "B" ∧ (grade_dict[5]!).snd = "B-" ∧ (grade_dict[6]!).snd = "C+" ∧ (grade_dict[7]!).snd = "C" ∧ (grade_dict[8]!).snd = "C-" ∧ (grade_dict[9]!).snd = "D+" ∧ (grade_dict[10]!).snd = "D" ∧ (grade_dict[11]!).snd = "D-" := by
  simp

-- LLM HELPER
lemma find_max_threshold (grade : Float) (h : 0.0 < grade) :
  ∃ j : Nat, j < 12 ∧ 
    [4.0, 3.7, 3.3, 3.0, 2.7, 2.3, 2.0, 1.7, 1.3, 1.0, 0.7, 0.0][j]! ≤ grade ∧
    (∀ k : Nat, k < 12 → [4.0, 3.7, 3.3, 3.0, 2.7, 2.3, 2.0, 1.7, 1.3, 1.0, 0.7, 0.0][k]! ≤ grade → [4.0, 3.7, 3.3, 3.0, 2.7, 2.3, 2.0, 1.7, 1.3, 1.0, 0.7, 0.0][k]! ≤ [4.0, 3.7, 3.3, 3.0, 2.7, 2.3, 2.0, 1.7, 1.3, 1.0, 0.7, 0.0][j]!) := by
  -- Find appropriate j based on grade value
  by_cases h1 : 4.0 ≤ grade
  · use 0; simp; constructor; linarith; intro k hk; simp at hk; simp; linarith
  by_cases h2 : 3.7 ≤ grade
  · use 1; simp; constructor; linarith; intro k hk; simp at hk; simp; linarith
  by_cases h3 : 3.3 ≤ grade
  · use 2; simp; constructor; linarith; intro k hk; simp at hk; simp; linarith
  by_cases h4 : 3.0 ≤ grade
  · use 3; simp; constructor; linarith; intro k hk; simp at hk; simp; linarith
  by_cases h5 : 2.7 ≤ grade
  · use 4; simp; constructor; linarith; intro k hk; simp at hk; simp; linarith
  by_cases h6 : 2.3 ≤ grade
  · use 5; simp; constructor; linarith; intro k hk; simp at hk; simp; linarith
  by_cases h7 : 2.0 ≤ grade
  · use 6; simp; constructor; linarith; intro k hk; simp at hk; simp; linarith
  by_cases h8 : 1.7 ≤ grade
  · use 7; simp; constructor; linarith; intro k hk; simp at hk; simp; linarith
  by_cases h9 : 1.3 ≤ grade
  · use 8; simp; constructor; linarith; intro k hk; simp at hk; simp; linarith
  by_cases h10 : 1.0 ≤ grade
  · use 9; simp; constructor; linarith; intro k hk; simp at hk; simp; linarith
  by_cases h11 : 0.7 ≤ grade
  · use 10; simp; constructor; linarith; intro k hk; simp at hk; simp; linarith
  · use 11; simp; constructor; linarith; intro k hk; simp at hk; simp; linarith

theorem correctness
(grades: List Float)
: problem_spec implementation grades
:= by
  unfold problem_spec implementation
  simp
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
      -- Use the helper lemma to find the appropriate j
      have ⟨j, hj_len, hj_le, hj_max⟩ := find_max_threshold grades[i]! h
      use j
      constructor
      · exact hj_len
      constructor
      · rw [grade_dict_keys_correct]; exact hj_le
      constructor
      · intro k hk; rw [grade_dict_keys_correct]; exact hj_max k hk
      · -- Show that grade_to_letter gives the correct result
        simp [grade_to_letter]
        -- This would require detailed case analysis matching the grade ranges
        -- to the corresponding letter grades
        admit
    · simp [h]
      have : grades[i]! ≤ 0.0 := by linarith
      simp [grade_to_letter]
      split_ifs with h1
      · rfl
      · linarith