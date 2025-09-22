-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countNumbersWithUniqueDigits (n : Nat) : Nat := sorry

theorem countNumbersWithUniqueDigits_positive (n : Nat) :
  countNumbersWithUniqueDigits n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem countNumbersWithUniqueDigits_monotonic (n : Nat) :
  n > 0 → countNumbersWithUniqueDigits n ≥ countNumbersWithUniqueDigits (n-1) := sorry

theorem countNumbersWithUniqueDigits_plateau (n : Nat) :
  n ≥ 10 → countNumbersWithUniqueDigits n = countNumbersWithUniqueDigits 10 := sorry

theorem countNumbersWithUniqueDigits_zero :
  countNumbersWithUniqueDigits 0 = 1 := sorry

theorem countNumbersWithUniqueDigits_one :
  countNumbersWithUniqueDigits 1 = 10 := sorry
-- </vc-theorems>