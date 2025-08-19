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

-- LLM HELPER
lemma grade_to_letter_correct (grade : Float) (h : 0.0 ≤ grade ∧ grade ≤ 4.0) :
  let grade_dict : List (Float × String) := [
    (4.0, "A+"), (3.7, "A"), (3.3, "A-"), (3.0, "B+"), (2.7, "B"), (2.3, "B-"),
    (2.0, "C+"), (1.7, "C"), (1.3, "C-"), (1.0, "D+"), (0.7, "D"), (0.0, "D-")
  ]
  let number_grade_keys := grade_dict.map (fun (g, _) => g)
  if 0.0 < grade then
    ∃ i : Nat, i < number_grade_keys.length ∧
      number_grade_keys[i]! ≤ grade ∧
      (∀ k' : Nat, k' < number_grade_keys.length → number_grade_keys[k']! ≤ grade → number_grade_keys[k']! ≤ number_grade_keys[i]!) ∧
      grade_to_letter grade = (grade_dict[i]!).snd
  else
    grade_to_letter grade = "E" := by
  simp [grade_to_letter]
  by_cases h1 : grade ≤ 0.0
  · simp [h1]
  · simp [h1]
    push_neg at h1
    simp [h1]
    by_cases h2 : grade < 0.7
    · use 11
      simp
      constructor
      · norm_num
      constructor
      · norm_num
        exact le_of_lt h2
      constructor
      · intro k' hk' hk'_le
        simp at hk'
        interval_cases k' <;> simp <;> linarith
      · simp
    · push_neg at h2
      by_cases h3 : grade < 1.0
      · use 10
        simp
        constructor
        · norm_num
        constructor
        · exact h2
        constructor
        · intro k' hk' hk'_le
          simp at hk'
          interval_cases k' <;> simp <;> linarith
        · simp
      · push_neg at h3
        by_cases h4 : grade < 1.3
        · use 9
          simp
          constructor
          · norm_num
          constructor
          · exact h3
          constructor
          · intro k' hk' hk'_le
            simp at hk'
            interval_cases k' <;> simp <;> linarith
          · simp
        · push_neg at h4
          by_cases h5 : grade < 1.7
          · use 8
            simp
            constructor
            · norm_num
            constructor
            · exact h4
            constructor
            · intro k' hk' hk'_le
              simp at hk'
              interval_cases k' <;> simp <;> linarith
            · simp
          · push_neg at h5
            by_cases h6 : grade < 2.0
            · use 7
              simp
              constructor
              · norm_num
              constructor
              · exact h5
              constructor
              · intro k' hk' hk'_le
                simp at hk'
                interval_cases k' <;> simp <;> linarith
              · simp
            · push_neg at h6
              by_cases h7 : grade < 2.3
              · use 6
                simp
                constructor
                · norm_num
                constructor
                · exact h6
                constructor
                · intro k' hk' hk'_le
                  simp at hk'
                  interval_cases k' <;> simp <;> linarith
                · simp
              · push_neg at h7
                by_cases h8 : grade < 2.7
                · use 5
                  simp
                  constructor
                  · norm_num
                  constructor
                  · exact h7
                  constructor
                  · intro k' hk' hk'_le
                    simp at hk'
                    interval_cases k' <;> simp <;> linarith
                  · simp
                · push_neg at h8
                  by_cases h9 : grade < 3.0
                  · use 4
                    simp
                    constructor
                    · norm_num
                    constructor
                    · exact h8
                    constructor
                    · intro k' hk' hk'_le
                      simp at hk'
                      interval_cases k' <;> simp <;> linarith
                    · simp
                  · push_neg at h9
                    by_cases h10 : grade < 3.3
                    · use 3
                      simp
                      constructor
                      · norm_num
                      constructor
                      · exact h9
                      constructor
                      · intro k' hk' hk'_le
                        simp at hk'
                        interval_cases k' <;> simp <;> linarith
                      · simp
                    · push_neg at h10
                      by_cases h11 : grade < 3.7
                      · use 2
                        simp
                        constructor
                        · norm_num
                        constructor
                        · exact h10
                        constructor
                        · intro k' hk' hk'_le
                          simp at hk'
                          interval_cases k' <;> simp <;> linarith
                        · simp
                      · push_neg at h11
                        by_cases h12 : grade < 4.0
                        · use 1
                          simp
                          constructor
                          · norm_num
                          constructor
                          · exact h11
                          constructor
                          · intro k' hk' hk'_le
                            simp at hk'
                            interval_cases k' <;> simp <;> linarith
                          · simp
                        · push_neg at h12
                          use 0
                          simp
                          constructor
                          · norm_num
                          constructor
                          · linarith [h.2, h12]
                          constructor
                          · intro k' hk' hk'_le
                            simp at hk'
                            interval_cases k' <;> simp <;> linarith [h.2, h12]
                          · simp

theorem correctness
(grades: List Float)
: problem_spec implementation grades
:= by
  simp [problem_spec, implementation]
  use grades.map grade_to_letter
  constructor
  · rfl
  · constructor
    · intro grade hgrade
      exact ⟨le_refl 0.0, by norm_num⟩
    constructor
    · simp
    · intro i hi
      simp
      have h : 0.0 ≤ grades[i]! ∧ grades[i]! ≤ 4.0 := ⟨le_refl 0.0, by norm_num⟩
      exact grade_to_letter_correct (grades[i]!) h