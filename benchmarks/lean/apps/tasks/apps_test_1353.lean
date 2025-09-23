-- <vc-preamble>
def ValidInput (n m a b : Int) : Prop :=
  n ≥ 1 ∧ n ≤ 1000 ∧
  m ≥ 1 ∧ m ≤ 1000 ∧
  a ≥ 1 ∧ a ≤ 1000 ∧
  b ≥ 1 ∧ b ≤ 1000

def OptimalCost (n m a b : Int) (h : ValidInput n m a b) : Int :=
  min (n * a) (min (((n + m - 1) / m) * b) ((n / m) * b + (n % m) * a))

@[reducible, simp]
def solve_precond (n m a b : Int) : Prop :=
  ValidInput n m a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m a b : Int) (h_precond : solve_precond n m a b) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m a b : Int) (result : Int) (h_precond : solve_precond n m a b) : Prop :=
  result ≥ 0 ∧ result = OptimalCost n m a b h_precond

theorem solve_spec_satisfied (n m a b : Int) (h_precond : solve_precond n m a b) :
    solve_postcond n m a b (solve n m a b h_precond) h_precond := by
  sorry
-- </vc-theorems>