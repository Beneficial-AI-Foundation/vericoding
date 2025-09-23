-- <vc-preamble>
def ValidInput (n k : Int) : Prop :=
  n ≥ 1 ∧ k ≥ 1 ∧ n ≤ 100 ∧ k ≤ 100

def MinCrackerDifference (n k : Int) : Int :=
  if n % k = 0 then 0 else 1

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
def solve_postcond (n k : Int) (result: Int) (h_precond : solve_precond n k) : Prop :=
  result = MinCrackerDifference n k ∧ 
  (result = 0 ↔ n % k = 0) ∧ 
  (result = 1 ↔ n % k ≠ 0)

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  sorry
-- </vc-theorems>