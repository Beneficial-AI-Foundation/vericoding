-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calcFuel (n : Nat) : FuelMap := sorry

theorem calc_fuel_values_nonneg (n : Nat) : 
  let result := calcFuel n
  result.lava ≥ 0 ∧ 
  result.blazeRod ≥ 0 ∧
  result.coal ≥ 0 ∧
  result.wood ≥ 0 ∧
  result.stick ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calc_fuel_total_seconds (n : Nat) :
  let result := calcFuel n
  result.lava * 800 + 
  result.blazeRod * 120 + 
  result.coal * 80 + 
  result.wood * 15 + 
  result.stick = n * 11 := sorry

theorem calc_fuel_stick_wood_optimal (n : Nat) :
  let result := calcFuel n
  result.stick < 15 := sorry

/-
info: expected
-/
-- #guard_msgs in
-- #eval calc_fuel 37

/-
info: expected
-/
-- #guard_msgs in
-- #eval calc_fuel 21

/-
info: expected
-/
-- #guard_msgs in
-- #eval calc_fuel 123
-- </vc-theorems>