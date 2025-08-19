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
  else
    let candidates := grade_dict.filter (fun (threshold, _) => threshold ≤ grade)
    match candidates.reverse.head? with
    | some (_, letter) => letter
    | none => "E"

def implementation (grades: List Float) : List String := 
  grades.map convert_grade

-- LLM HELPER
theorem convert_grade_correct (grade : Float) : 
  let number_grade_keys := grade_dict.map (fun (g, _) => g)
  if 0.0 < grade then
    ∃ i : Nat, i < number_grade_keys.length ∧
      number_grade_keys[i]! ≤ grade ∧
      (∀ k' : Nat, k' < number_grade_keys.length → number_grade_keys[k']! ≤ grade → number_grade_keys[k']! ≤ number_grade_keys[i]!) ∧
      convert_grade grade = (grade_dict[i]!).snd
  else
    convert_grade grade = "E" := by
  simp [convert_grade, grade_dict]
  split_ifs with h
  · simp [h]
  · sorry

theorem correctness
(grades: List Float)
: problem_spec implementation grades := by
  simp [problem_spec, implementation]
  use grades.map convert_grade
  constructor
  · rfl
  · constructor
    · sorry -- grades.all condition
    · constructor
      · simp [List.length_map]
      · intro i hi
        simp [List.get_map]
        exact convert_grade_correct (grades[i]!)