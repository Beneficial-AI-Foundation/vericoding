-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def final_grade (exam : Int) (projects : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem final_grade_output_range (exam : Int) (projects : Int) :
  final_grade exam projects = 0 ∨ 
  final_grade exam projects = 75 ∨
  final_grade exam projects = 90 ∨ 
  final_grade exam projects = 100 :=
sorry

theorem final_grade_high_scores (exam projects : Int) :
  (exam > 90 ∨ projects > 10) → final_grade exam projects = 100 :=
sorry

theorem final_grade_medium_high_scores (exam projects : Int) :
  (exam > 75 ∧ exam ≤ 90 ∧ projects ≥ 5 ∧ projects ≤ 10) → 
  final_grade exam projects = 90 :=
sorry

theorem final_grade_medium_scores (exam projects : Int) :
  (exam > 50 ∧ exam ≤ 75 ∧ projects ≥ 2 ∧ projects ≤ 4) → 
  final_grade exam projects = 75 :=
sorry

theorem final_grade_low_scores (exam projects : Int) :
  (exam ≤ 50 ∧ projects ≤ 1) → final_grade exam projects = 0 :=
sorry

theorem final_grade_high_exam (exam projects : Int) :
  exam > 90 → final_grade exam projects = 100 :=
sorry

theorem final_grade_many_projects (exam projects : Int) :
  projects > 10 → final_grade exam projects = 100 :=
sorry

theorem final_grade_low_both (exam projects : Int) :
  exam ≤ 50 ∧ projects ≤ 1 → final_grade exam projects = 0 :=
sorry
-- </vc-theorems>