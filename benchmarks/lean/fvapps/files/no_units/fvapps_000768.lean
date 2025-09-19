-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumFirstLastDigit (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_first_last_digit_in_range (n : Nat) (h : n > 0) :
  let result := sumFirstLastDigit n
  result ≥ 0 ∧ result ≤ 18
  := sorry

theorem single_digit_sum_is_double (n : Nat) (h1 : n > 0) (h2 : n ≤ 9) :
  sumFirstLastDigit n = n + n
  := sorry
-- </vc-theorems>