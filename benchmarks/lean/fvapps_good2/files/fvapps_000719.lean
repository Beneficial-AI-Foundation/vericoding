-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_army_power (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem army_power_always_positive (n : Nat) (h : n ≥ 1) :
  calc_army_power n ≥ 1 :=
sorry

theorem army_power_monotonic (n : Nat) (h : n > 1) :
  calc_army_power n ≥ calc_army_power (n-1) :=
sorry

theorem army_power_base_cases :
  (calc_army_power 1 = 1) ∧ (calc_army_power 4 = 2) :=
sorry

theorem army_power_bounded (n : Nat) (h : n ≥ 1) :
  calc_army_power n ≤ n :=
sorry
-- </vc-theorems>