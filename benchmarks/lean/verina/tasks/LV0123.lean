-- <vc-preamble>
@[reducible, simp]
def sumOfFourthPowerOfOddNumbers_precond (n : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumOfFourthPowerOfOddNumbers (n : Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def sumOfFourthPowerOfOddNumbers_postcond (n : Nat) (result: Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :=
  15 * result = n * (2 * n + 1) * (7 + 24 * n^3 - 12 * n^2 - 14 * n)

theorem sumOfFourthPowerOfOddNumbers_spec_satisfied (n: Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :
    sumOfFourthPowerOfOddNumbers_postcond (n) (sumOfFourthPowerOfOddNumbers (n) h_precond) h_precond := by
  sorry
-- </vc-theorems>