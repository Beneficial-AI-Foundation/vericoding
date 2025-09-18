-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def distance (n : Nat) : Nat := sorry

theorem distance_nonnegative (n : Nat) :
  n > 0 → distance n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem distance_growth_rate (n : Nat) :
  n > 0 → distance (2 * n) ≥ distance n / 2 := sorry

theorem distance_at_center :
  distance 1 = 0 := sorry

theorem distance_away_from_center (n : Nat) :
  n > 1 → distance n > 0 := sorry

theorem distance_triangle_inequality (n : Nat) :
  n > 1 → distance n ≤ distance (n-1) + 1 ∧ distance n ≤ distance (n+1) + 1 := sorry
-- </vc-theorems>