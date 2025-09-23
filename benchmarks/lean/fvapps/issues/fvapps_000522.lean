-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_min_weapons (n k : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_weapons_div (n k : Nat) (h : n > 0) :
  calculate_min_weapons n k = k / n :=
sorry

theorem min_weapons_nonneg (n k : Nat) (h : n > 0) :
  calculate_min_weapons n k ≥ 0 :=
sorry

theorem min_weapons_times_n_le (n k : Nat) (h : n > 0) :
  (calculate_min_weapons n k) * n ≤ k :=
sorry

theorem min_weapons_plus_one_gt (n k : Nat) (h : n > 0) (h2 : k % n ≠ 0) :
  (calculate_min_weapons n k + 1) * n > k :=
sorry

theorem min_weapons_zero (n : Nat) (h : n > 0) :
  calculate_min_weapons n 0 = 0 :=
sorry

theorem min_weapons_zero_n (k : Nat) :
  calculate_min_weapons 0 k = 0 ∨ calculate_min_weapons 0 k = undefined :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval calculate_min_weapons 5 8

/-
info: 2
-/
-- #guard_msgs in
-- #eval calculate_min_weapons 3 7

/-
info: 2
-/
-- #guard_msgs in
-- #eval calculate_min_weapons 10 25
-- </vc-theorems>