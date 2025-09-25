-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_finite_fraction (p q b : Int) : Bool := sorry

theorem sign_invariance (p q b : Int) 
  (h1: q ≠ 0) (h2: b > 0) :
  is_finite_fraction p q b = is_finite_fraction (-p) q b := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem finite_power_of_two (p power : Int)
  (h1: p > 0) (h2: power > 0) :
  let nat_power := Int.toNat power
  is_finite_fraction p (Int.pow 2 nat_power) 10 = true := sorry 

theorem finite_power_of_five (p power : Int)
  (h1: p > 0) (h2: power > 0) : 
  let nat_power := Int.toNat power
  is_finite_fraction p (Int.pow 5 nat_power) 10 = true := sorry
-- </vc-theorems>