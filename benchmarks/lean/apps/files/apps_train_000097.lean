-- <vc-helpers>
-- </vc-helpers>

def max_perfect_teams (c m x : Nat) : Nat :=
  sorry

theorem max_perfect_teams_non_negative (c m x : Nat) :
  max_perfect_teams c m x ≥ 0 := 
  sorry

theorem max_perfect_teams_bound_by_c (c m x : Nat) :
  max_perfect_teams c m x ≤ c :=
  sorry

theorem max_perfect_teams_bound_by_m (c m x : Nat) :
  max_perfect_teams c m x ≤ m :=
  sorry

theorem max_perfect_teams_total_specialists (c m x : Nat) :
  (max_perfect_teams c m x) * 3 ≤ c + m + x :=
  sorry

theorem max_perfect_teams_is_maximal (c m x : Nat) :
  max_perfect_teams c m x = min (min c m) ((c + m + x) / 3) :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval max_perfect_teams 1 1 1

/-
info: 3
-/
-- #guard_msgs in
-- #eval max_perfect_teams 3 6 0

/-
info: 0
-/
-- #guard_msgs in
-- #eval max_perfect_teams 0 0 0

/-
info: 0
-/
-- #guard_msgs in
-- #eval max_perfect_teams 0 1 1

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible