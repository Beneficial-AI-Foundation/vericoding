-- <vc-helpers>
-- </vc-helpers>

def get_score (n : Int) : Int := sorry

theorem get_score_returns_integer (n : Int) :
  get_score n = get_score n := by sorry

theorem get_score_non_negative (n : Int) (h : n ≥ 0) :
  get_score n ≥ 0 := by sorry

theorem get_score_monotonic (a b : Int) (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a < b) :
  get_score a < get_score b := by sorry

theorem get_score_formula (n : Int) :
  get_score n = n * (n + 1) * 25 := by sorry

/-
info: 50
-/
-- #guard_msgs in
-- #eval get_score 1

/-
info: 150
-/
-- #guard_msgs in
-- #eval get_score 2

/-
info: 750
-/
-- #guard_msgs in
-- #eval get_score 5

-- Apps difficulty: introductory
-- Assurance level: guarded