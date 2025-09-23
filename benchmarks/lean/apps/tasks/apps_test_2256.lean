-- <vc-preamble>
def ValidInput (n x a b : Int) : Prop :=
  2 ≤ n ∧ n ≤ 100 ∧ 0 ≤ x ∧ x ≤ 100 ∧ 1 ≤ a ∧ a ≤ n ∧ 1 ≤ b ∧ b ≤ n ∧ a ≠ b

def MaxDistance (n x a b : Int) (h : ValidInput n x a b) : Int :=
  let initialDistance := if a ≥ b then a - b else b - a
  let maxPossibleDistance := initialDistance + x
  let maxLineDistance := n - 1
  if maxPossibleDistance ≤ maxLineDistance then maxPossibleDistance else maxLineDistance

def ValidResult (n x a b result : Int) (h : ValidInput n x a b) : Prop :=
  result = MaxDistance n x a b h ∧ 0 ≤ result ∧ result ≤ n - 1

@[reducible, simp]
def solve_precond (n x a b : Int) : Prop :=
  ValidInput n x a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n x a b : Int) (h_precond : solve_precond n x a b) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n x a b : Int) (result : Int) (h_precond : solve_precond n x a b) : Prop :=
  ValidResult n x a b result h_precond ∧ result ≥ 0

theorem solve_spec_satisfied (n x a b : Int) (h_precond : solve_precond n x a b) :
    solve_postcond n x a b (solve n x a b h_precond) h_precond := by
  sorry
-- </vc-theorems>