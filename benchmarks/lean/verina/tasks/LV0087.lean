-- <vc-preamble>
@[reducible, simp]
def sumOfSquaresOfFirstNOddNumbers_precond (n : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumOfSquaresOfFirstNOddNumbers (n : Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def sumOfSquaresOfFirstNOddNumbers_postcond (n : Nat) (result: Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) :=
  result - (n * (2 * n - 1) * (2 * n + 1)) / 3 = 0 ∧
  (n * (2 * n - 1) * (2 * n + 1)) / 3 - result = 0

theorem sumOfSquaresOfFirstNOddNumbers_spec_satisfied (n: Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) :
    sumOfSquaresOfFirstNOddNumbers_postcond (n) (sumOfSquaresOfFirstNOddNumbers (n) h_precond) h_precond := by
  sorry
-- </vc-theorems>