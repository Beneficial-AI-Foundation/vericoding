-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_perfect_teams (c m x : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>