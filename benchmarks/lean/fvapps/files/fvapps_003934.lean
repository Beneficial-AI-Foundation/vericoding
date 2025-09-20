-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_digits (n : Int) : Int :=
  sorry

def sum_of_digits_string (n : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_digits_nonnegative (x : Int) :
  sum_digits x ≥ 0 :=
sorry

theorem sum_digits_symmetric (x : Int) :
  sum_digits x = sum_digits (-x) :=
sorry

theorem sum_digits_less_than_input (x : Int) (h : x.natAbs > 9) :
  sum_digits x < x.natAbs :=
sorry

theorem sum_digits_single_digit (x : Int)
  (h : 0 ≤ x.natAbs ∧ x.natAbs ≤ 9) :
  sum_digits x = x.natAbs :=
sorry

theorem sum_digits_matches_string_sum (x : Int) :
  x ≥ 0 → sum_digits x = sum_of_digits_string x :=
sorry
-- </vc-theorems>