-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_height_eligibility (height min_height : Int) : String := sorry

def process_test_cases (cases : List (Int × Int)) : List String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_height_eligibility_valid (height min_height : Int) :
  let result := check_height_eligibility height min_height
  result = "Yes" ∨ result = "No" ∧ 
  (result = "Yes" ↔ height ≥ min_height) := sorry

theorem process_test_cases_length (cases : List (Int × Int)) :
  (process_test_cases cases).length = cases.length := sorry

theorem process_test_cases_valid_outputs (cases : List (Int × Int)) :
  ∀ x ∈ process_test_cases cases, x = "Yes" ∨ x = "No" := sorry

theorem process_test_cases_correct (cases : List (Int × Int)) (i : Nat) (h : i < cases.length) :
  let result := (process_test_cases cases)[i]'(by rw [process_test_cases_length]; exact h)
  let case := cases[i]'h
  result = (if case.1 ≥ case.2 then "Yes" else "No") := sorry

/-
info: ['Yes', 'No']
-/
-- #guard_msgs in
-- #eval process_test_cases [(120, 100), (90, 100)]

/-
info: ['Yes']
-/
-- #guard_msgs in
-- #eval process_test_cases [(100, 100)]

/-
info: ['Yes', 'No', 'Yes']
-/
-- #guard_msgs in
-- #eval process_test_cases [(150, 120), (80, 90), (200, 200)]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded