-- <vc-helpers>
-- </vc-helpers>

def grader (score : Float) : String := sorry

theorem grader_A {score : Float} (h : score ≥ 0.9 ∧ score ≤ 1.0) : 
  grader score = "A" := sorry

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

/-
info: 'A'
-/
-- #guard_msgs in
-- #eval grader 0.95

/-
info: 'B'
-/
-- #guard_msgs in
-- #eval grader 0.85

/-
info: 'C'
-/
-- #guard_msgs in
-- #eval grader 0.75

/-
info: 'D'
-/
-- #guard_msgs in
-- #eval grader 0.65

/-
info: 'A'
-/
-- #guard_msgs in
-- #eval grader 1.0

/-
info: 'F'
-/
-- #guard_msgs in
-- #eval grader 0.0

/-
info: 'F'
-/
-- #guard_msgs in
-- #eval grader 1.1

/-
info: 'A'
-/
-- #guard_msgs in
-- #eval grader 0.9

/-
info: 'B'
-/
-- #guard_msgs in
-- #eval grader 0.8

/-
info: 'C'
-/
-- #guard_msgs in
-- #eval grader 0.7

/-
info: 'D'
-/
-- #guard_msgs in
-- #eval grader 0.6

-- Apps difficulty: introductory
-- Assurance level: unguarded