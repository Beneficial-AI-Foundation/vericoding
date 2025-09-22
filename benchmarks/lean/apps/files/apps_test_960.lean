-- <vc-preamble>
def ValidInput (n k : Int) : Prop :=
  n ≥ 1 ∧ k ≥ 2

def SatisfiesConstraint (x n k : Int) : Prop :=
  x > 0 ∧ k > 0 ∧ (x / k) * (x % k) = n

@[reducible, simp]
def solve_precond (n k : Int) : Prop :=
  ValidInput n k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (h_precond : solve_precond n k) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (result : Int) (h_precond : solve_precond n k) : Prop :=
  result > 0 ∧ SatisfiesConstraint result n k ∧ (∀ x, x > 0 ∧ (x / k) * (x % k) = n → result ≤ x)

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  sorry
-- </vc-theorems>