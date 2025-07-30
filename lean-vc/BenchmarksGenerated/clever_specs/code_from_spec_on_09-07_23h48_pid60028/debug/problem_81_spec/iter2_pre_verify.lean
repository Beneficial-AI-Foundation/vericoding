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
lemma convert_grade_case_analysis (grade : Float) (h_valid : 0.0 ≤ grade ∧ grade ≤ 4.0) :
  let result := convert_grade grade
  let number_grade_keys := grade_dict.map (fun (g, _) => g)
  if 0.0 < grade then
    ∃ i : Nat, i < number_grade_keys.length ∧
      number_grade_keys[i]! ≤ grade ∧
      (∀ k' : Nat, k' < number_grade_keys.length → number_grade_keys[k']! ≤ grade → number_grade_keys[k']! ≤ number_grade_keys[i]!) ∧
      result = (grade_dict[i]!).snd
  else
    result = "E" := by
  simp [convert_grade, grade_dict, number_grade_keys]
  split_ifs with h
  · rfl
  · push_neg at h
    have h_pos : 0.0 < grade := h
    simp
    by_cases h1 : grade ≥ 4.0
    · simp [h1]
      use 0
      simp
      constructor
      · norm_num
      constructor
      · exact h1
      constructor
      · intro k' hk' hle
        simp at hle ⊢
        interval_cases k' <;> simp at hle ⊢ <;> linarith
      · rfl
    · push_neg at h1
      by_cases h2 : grade ≥ 3.7
      · simp [h1, h2]
        use 1
        simp
        constructor
        · norm_num
        constructor
        · exact h2
        constructor
        · intro k' hk' hle
          simp at hle ⊢
          interval_cases k' <;> simp at hle ⊢ <;> linarith
        · rfl
      · push_neg at h2
        by_cases h3 : grade ≥ 3.3
        · simp [h1, h2, h3]
          use 2
          simp
          constructor
          · norm_num
          constructor
          · exact h3
          constructor
          · intro k' hk' hle
            simp at hle ⊢
            interval_cases k' <;> simp at hle ⊢ <;> linarith
          · rfl
        · push_neg at h3
          by_cases h4 : grade ≥ 3.0
          · simp [h1, h2, h3, h4]
            use 3
            simp
            constructor
            · norm_num
            constructor
            · exact h4
            constructor
            · intro k' hk' hle
              simp at hle ⊢
              interval_cases k' <;> simp at hle ⊢ <;> linarith
            · rfl
          · push_neg at h4
            by_cases h5 : grade ≥ 2.7
            · simp [h1, h2, h3, h4, h5]
              use 4
              simp
              constructor
              · norm_num
              constructor
              · exact h5
              constructor
              · intro k' hk' hle
                simp at hle ⊢
                interval_cases k' <;> simp at hle ⊢ <;> linarith
              · rfl
            · push_neg at h5
              by_cases h6 : grade ≥ 2.3
              · simp [h1, h2, h3, h4, h5, h6]
                use 5
                simp
                constructor
                · norm_num
                constructor
                · exact h6
                constructor
                · intro k' hk' hle
                  simp at hle ⊢
                  interval_cases k' <;> simp at hle ⊢ <;> linarith
                · rfl
              · push_neg at h6
                by_cases h7 : grade ≥ 2.0
                · simp [h1, h2, h3, h4, h5, h6, h7]
                  use 6
                  simp
                  constructor
                  · norm_num
                  constructor
                  · exact h7
                  constructor
                  · intro k' hk' hle
                    simp at hle ⊢
                    interval_cases k' <;> simp at hle ⊢ <;> linarith
                  · rfl
                · push_neg at h7
                  by_cases h8 : grade ≥ 1.7
                  · simp [h1, h2, h3, h4, h5, h6, h7, h8]
                    use 7
                    simp
                    constructor
                    · norm_num
                    constructor
                    · exact h8
                    constructor
                    · intro k' hk' hle
                      simp at hle ⊢
                      interval_cases k' <;> simp at hle ⊢ <;> linarith
                    · rfl
                  · push_neg at h8
                    by_cases h9 : grade ≥ 1.3
                    · simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]
                      use 8
                      simp
                      constructor
                      · norm_num
                      constructor
                      · exact h9
                      constructor
                      · intro k' hk' hle
                        simp at hle ⊢
                        interval_cases k' <;> simp at hle ⊢ <;> linarith
                      · rfl
                    · push_neg at h9
                      by_cases h10 : grade ≥ 1.0
                      · simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
                        use 9
                        simp
                        constructor
                        · norm_num
                        constructor
                        · exact h10
                        constructor
                        · intro k' hk' hle
                          simp at hle ⊢
                          interval_cases k' <;> simp at hle ⊢ <;> linarith
                        · rfl
                      · push_neg at h10
                        by_cases h11 : grade ≥ 0.7
                        · simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
                          use 10
                          simp
                          constructor
                          · norm_num
                          constructor
                          · exact h11
                          constructor
                          · intro k' hk' hle
                            simp at hle ⊢
                            interval_cases k' <;> simp at hle ⊢ <;> linarith
                          · rfl
                        · push_neg at h11
                          simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
                          use 11
                          simp
                          constructor
                          · norm_num
                          constructor
                          · exact h_valid.1
                          constructor
                          · intro k' hk' hle
                            simp at hle ⊢
                            interval_cases k' <;> simp at hle ⊢ <;> linarith
                          · rfl

theorem correctness
(grades: List Float)
: problem_spec implementation grades := by
  simp [problem_spec]
  use grades.map convert_grade
  constructor
  · rfl
  · simp [implementation]
    constructor
    · intro grade hgrade
      -- For the spec to make sense, we need to assume grades are valid
      simp
      constructor
      · norm_num
      · norm_num
    constructor
    · simp [List.length_map]
    · intro i hi
      simp [List.getElem_map]
      apply convert_grade_case_analysis
      simp
      constructor
      · norm_num
      · norm_num