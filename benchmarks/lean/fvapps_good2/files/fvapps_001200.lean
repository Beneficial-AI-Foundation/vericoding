-- <vc-preamble>
def contains_five_or_zero (s : String) : Bool :=
  s.contains '0' || s.contains '5'
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_divisible_by_five : String → Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_divisible_outputs_zero_or_one (s : String) :
  (check_divisible_by_five s = 0) ∨ (check_divisible_by_five s = 1) :=
sorry

theorem check_divisible_leading_zero (s : String) :
  check_divisible_by_five ("0" ++ s) = 1 :=
sorry
-- </vc-theorems>