-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getSumOfDigits (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_digits_basic_property (n : Nat) :
  getSumOfDigits n ≤ n :=
  sorry

theorem sum_digits_upper_bound (n : Nat) :
  getSumOfDigits n ≤ 9 * (toString n).length :=
  sorry

theorem sum_digits_non_negative (n : Nat) :
  getSumOfDigits n ≥ 0 :=
  sorry

theorem single_digit_identity (n : Nat) :
  n < 10 → getSumOfDigits n = n :=
  sorry
-- </vc-theorems>