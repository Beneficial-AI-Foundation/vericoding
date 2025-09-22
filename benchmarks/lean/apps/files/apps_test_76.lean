-- <vc-preamble>
def ValidInput (n m a b : Int) : Prop :=
  n ≥ 1 ∧ m ≥ 1 ∧ a ≥ 1 ∧ b ≥ 1

def MinCostToDivisible (n m a b : Int) : Int :=
  let k := n % m
  if k * b < (m - k) * a then k * b else (m - k) * a

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
  result = MinCostToDivisible n m a b ∧ result ≥ 0

theorem solve_spec_satisfied (n m a b : Int) (h_precond : solve_precond n m a b) :
    solve_postcond n m a b (solve n m a b h_precond) h_precond := by
  sorry
-- </vc-theorems>