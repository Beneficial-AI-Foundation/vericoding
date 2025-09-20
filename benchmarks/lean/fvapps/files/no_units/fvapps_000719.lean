-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_army_power (n : Nat) : Nat := sorry

/- The army power is always at least 1 for positive inputs -/
-- </vc-definitions>

-- <vc-theorems>
theorem army_power_always_positive (n : Nat) (h : n ≥ 1) : 
  calc_army_power n ≥ 1 := sorry
-- </vc-theorems>