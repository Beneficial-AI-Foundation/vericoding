-- <vc-helpers>
-- </vc-helpers>

def calc_ms (n : Int) : Int := sorry

theorem calc_ms_positive (n : Nat) : calc_ms n > 0 := sorry

theorem calc_ms_equals_twenty_pow (n : Nat) : calc_ms n = 20 ^ n := sorry

theorem calc_ms_growth (n : Nat) : n < 5 → calc_ms (n + 1) > calc_ms n := sorry

theorem calc_ms_base : calc_ms 0 = 1 := sorry

theorem calc_ms_power (n₁ n₂ : Nat) : calc_ms (n₁ + n₂) = calc_ms n₁ * calc_ms n₂ := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval calc_ms 0

/-
info: 20
-/
-- #guard_msgs in
-- #eval calc_ms 1

/-
info: 8000
-/
-- #guard_msgs in
-- #eval calc_ms 3

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible