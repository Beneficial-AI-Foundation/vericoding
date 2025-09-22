-- <vc-preamble>
@[reducible, simp]  
def integerSquareRoot_precond (n : Int) := n ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def integerSquareRoot (n : Int) (h_precond : integerSquareRoot_precond (n)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def integerSquareRoot_postcond (n : Int) (result: Int) (h_precond : integerSquareRoot_precond (n)) :=
  0 ≤ result * result ∧ result * result ≤ n ∧ n < (result + 1) * (result + 1)

theorem integerSquareRoot_spec_satisfied (n: Int) (h_precond : integerSquareRoot_precond (n)) :
    integerSquareRoot_postcond (n) (integerSquareRoot (n) h_precond) h_precond := by
  sorry
-- </vc-theorems>