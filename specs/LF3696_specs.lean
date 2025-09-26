-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def grader (score : Float) : String := sorry

theorem grader_A {score : Float} (h : score ≥ 0.9 ∧ score ≤ 1.0) : 
  grader score = "A" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem grader_B {score : Float} (h : score ≥ 0.8 ∧ score < 0.9) : 
  grader score = "B" := sorry

theorem grader_C {score : Float} (h : score ≥ 0.7 ∧ score < 0.8) :
  grader score = "C" := sorry

theorem grader_D {score : Float} (h : score ≥ 0.6 ∧ score < 0.7) :
  grader score = "D" := sorry

theorem grader_F {score : Float} (h : score < 0.6 ∨ score > 1.0) :
  grader score = "F" := sorry

theorem grader_returns_valid_grade (score : Float) :
  grader score ∈ ["A", "B", "C", "D", "F"] := sorry
-- </vc-theorems>