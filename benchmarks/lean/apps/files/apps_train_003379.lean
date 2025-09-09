-- <vc-helpers>
-- </vc-helpers>

def distance (n : Nat) : Nat := sorry

theorem distance_nonnegative (n : Nat) :
  n > 0 → distance n ≥ 0 := sorry

theorem distance_growth_rate (n : Nat) :
  n > 0 → distance (2 * n) ≥ distance n / 2 := sorry

theorem distance_at_center :
  distance 1 = 0 := sorry

theorem distance_away_from_center (n : Nat) :
  n > 1 → distance n > 0 := sorry

theorem distance_triangle_inequality (n : Nat) :
  n > 1 → distance n ≤ distance (n-1) + 1 ∧ distance n ≤ distance (n+1) + 1 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval distance 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval distance 5

/-
info: 4
-/
-- #guard_msgs in
-- #eval distance 25

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible