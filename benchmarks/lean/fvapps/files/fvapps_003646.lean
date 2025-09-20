-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def largest_power (n: Nat) : Nat × Int := sorry

theorem largest_power_output_format (n: Nat) (h: n ≥ 1) :
  let result := largest_power n
  Nat.zero ≤ result.1 ∧ result.1 < n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem largest_power_special_cases :
  largest_power 1 = (0, -1) ∧ 
  largest_power 2 = (1, -1) ∧
  largest_power 3 = (1, -1) ∧ 
  largest_power 4 = (1, -1) := sorry

theorem largest_power_bounds (n: Nat) (h: n ≥ 5) :
  let result := largest_power n
  0 < result.1 ∧ result.1 < n ∧ 
  (result.2 > 0 ∨ result.2 = -1) := sorry

theorem largest_power_is_maximal (n: Nat) (h: n ≥ 5) :
  let result := largest_power n
  ∀ base exp : Nat, base ≥ 2 → exp ≥ 2 →
  base ^ exp < n → base ^ exp ≤ result.1 := sorry
-- </vc-theorems>