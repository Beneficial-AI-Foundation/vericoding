-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_ms (n : Int) : Int := sorry

theorem calc_ms_positive (n : Nat) : calc_ms n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calc_ms_equals_twenty_pow (n : Nat) : calc_ms n = 20 ^ n := sorry

theorem calc_ms_growth (n : Nat) : n < 5 → calc_ms (n + 1) > calc_ms n := sorry

theorem calc_ms_base : calc_ms 0 = 1 := sorry

theorem calc_ms_power (n₁ n₂ : Nat) : calc_ms (n₁ + n₂) = calc_ms n₁ * calc_ms n₂ := sorry
-- </vc-theorems>