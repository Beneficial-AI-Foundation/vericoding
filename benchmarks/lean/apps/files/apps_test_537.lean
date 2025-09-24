-- <vc-preamble>
def ValidInput (n k : Int) : Prop :=
  n ≥ 0 ∧ k ≥ 0 ∧ k + 1 > 0

def ValidOutput (result : List Int) (n k : Int) : Prop :=
  result.length = 3 ∧
  result[0]! ≥ 0 ∧ result[1]! ≥ 0 ∧ result[2]! ≥ 0 ∧
  result[1]! = result[0]! * k ∧
  result[0]! + result[1]! ≤ n / 2 ∧
  result[2]! = n - result[0]! - result[1]!

def OptimalDiplomas (n k : Int) : Int :=
  (n / 2) / (k + 1)

@[reducible, simp]
def solve_precond (n k : Int) : Prop :=
  ValidInput n k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (h_precond : solve_precond n k) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (result : List Int) (h_precond : solve_precond n k) : Prop :=
  ValidOutput result n k ∧ result[0]! = OptimalDiplomas n k

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  sorry
-- </vc-theorems>