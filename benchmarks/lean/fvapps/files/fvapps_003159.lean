-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def faulty_odometer (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem odometer_never_negative (n : Nat) : 
  faulty_odometer n ≥ 0 :=
sorry

theorem odometer_always_smaller (n : Nat) :
  faulty_odometer n ≤ n :=
sorry

theorem odometer_consistent (n : Nat) :
  faulty_odometer n = faulty_odometer n :=
sorry

theorem odometer_zero :
  faulty_odometer 0 = 0 :=
sorry
-- </vc-theorems>