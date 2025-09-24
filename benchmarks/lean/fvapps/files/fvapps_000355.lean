-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_measure_water (x y z : Nat) : Bool := sorry

def gcd (a b : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem measurement_bounds {x y z : Nat} :
  can_measure_water x y z → z ≤ x + y ∧ z ≥ 0 := sorry

theorem zero_target_always_possible {x y : Nat} :
  can_measure_water x y 0 = true := sorry

theorem single_jug_measurements {cap : Nat} (h : cap > 0) :
  can_measure_water cap 0 cap = true ∧
  can_measure_water cap 0 (cap + 1) = false := sorry

theorem commutative {x y z : Nat} :
  can_measure_water x y z = can_measure_water y x z := sorry

theorem gcd_property {x y z : Nat} (hx : x > 0) (hy : y > 0) :
  can_measure_water x y z → z % gcd x y = 0 := sorry
-- </vc-theorems>