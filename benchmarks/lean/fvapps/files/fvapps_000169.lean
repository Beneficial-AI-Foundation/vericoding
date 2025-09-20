-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxDiff (n : Nat) : Nat :=
sorry

def numDigits (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxDiff_single_digit (n : Nat) (h : n < 10) : maxDiff n = 8 :=
sorry

theorem maxDiff_properties (n : Nat) :
  n ≥ 10 →
  maxDiff n ≥ 0 ∧
  maxDiff n ≤ 999999 :=
sorry

theorem maxDiff_nonnegative (n : Nat) : maxDiff n ≥ 0 :=
sorry
-- </vc-theorems>