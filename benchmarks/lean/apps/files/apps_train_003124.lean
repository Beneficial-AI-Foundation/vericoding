-- <vc-helpers>
-- </vc-helpers>

def enough (cap on wait : Nat) : Nat := sorry

theorem enough_nonneg (cap on wait : Nat) :
  cap > 0 → enough cap on wait ≥ 0 := sorry

theorem enough_fits (cap on wait : Nat) :
  cap > 0 → on + wait ≤ cap → enough cap on wait = 0 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval enough 10 5 5

/-
info: 10
-/
-- #guard_msgs in
-- #eval enough 100 60 50

/-
info: 0
-/
-- #guard_msgs in
-- #eval enough 20 5 5

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible