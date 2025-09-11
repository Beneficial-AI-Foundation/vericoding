-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def LetterGrade := Char

def calculate_grade (scores : List Nat) : LetterGrade :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem grade_is_valid_letter (scores : List Nat) (h : scores ≠ []) : 
  let grade := calculate_grade scores
  grade = 'F' ∨ grade = 'D' ∨ grade = 'C' ∨ grade = 'B' ∨ grade = 'A' :=
sorry

theorem all_high_scores_get_a (scores : List Nat) (h : scores ≠ []) :
  (∀ x ∈ scores, x = 95) →
  calculate_grade scores = 'A' :=
sorry

theorem all_low_scores_get_f (scores : List Nat) (h : scores ≠ []) :
  (∀ x ∈ scores, x = 50) →
  calculate_grade scores = 'F' :=
sorry

/-
info: 'A'
-/
-- #guard_msgs in
-- #eval calculate_grade [92, 94, 99]

/-
info: 'C'
-/
-- #guard_msgs in
-- #eval calculate_grade [50, 60, 70, 80, 90]

/-
info: 'F'
-/
-- #guard_msgs in
-- #eval calculate_grade [50, 55]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded