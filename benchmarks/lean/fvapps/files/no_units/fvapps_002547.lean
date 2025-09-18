-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def race (v1 v2 g : Nat) : Option (Nat × Nat × Nat) := sorry

theorem race_slower_returns_none {v1 v2 g : Nat} :
  v2 ≤ v1 → race v1 v2 g = none := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem race_result_non_negative {v1 v2 g : Nat} 
  (h : v2 > v1) (result : Nat × Nat × Nat) :
  race v1 v2 g = some result →
  result.1 ≥ 0 ∧ result.2.1 ≥ 0 ∧ result.2.2 ≥ 0 := sorry

theorem race_result_valid_minutes_seconds {v1 v2 g : Nat}
  (h : v2 > v1) (result : Nat × Nat × Nat) :
  race v1 v2 g = some result →
  result.2.1 < 60 ∧ result.2.2 < 60 := sorry

theorem race_satisfies_distance_equation {v1 v2 g : Nat}
  (h : v2 > v1) (result : Nat × Nat × Nat) :
  race v1 v2 g = some result →
  (result.1 * 3600 + result.2.1 * 60 + result.2.2) * (v2 - v1) = g * 3600 := sorry
-- </vc-theorems>