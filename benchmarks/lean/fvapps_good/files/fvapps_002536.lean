-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def zeroFuel (distance mpg fuel : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_fuel_main_property {distance mpg fuel : Nat} (h : mpg > 0) :
  zeroFuel distance mpg fuel = (fuel * mpg ≥ distance) :=
  sorry

theorem zero_fuel_no_gas {distance mpg : Nat} (h : mpg > 0) :
  distance > 0 → ¬(zeroFuel distance mpg 0) :=
  sorry

theorem zero_distance_any_fuel {mpg fuel : Nat} (h : mpg > 0) :
  zeroFuel 0 mpg fuel :=
  sorry
-- </vc-theorems>