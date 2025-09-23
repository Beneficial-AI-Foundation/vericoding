-- <vc-preamble>
def ValidInput (n : Int) (k : Int) (requests : List Int) : Prop :=
  n ≥ 1 ∧ k ≥ 1 ∧ requests.length = n ∧
  ∀ i, 0 ≤ i ∧ i < requests.length → 1 ≤ requests[i]! ∧ requests[i]! ≤ n

def ValidSolution (n : Int) (k : Int) (requests : List Int) (cost : Int) : Prop :=
  ValidInput n k requests ∧ cost ≥ 0 ∧ cost ≤ n

@[reducible, simp]
def solve_precond (n : Int) (k : Int) (requests : List Int) : Prop :=
  ValidInput n k requests
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (k : Int) (requests : List Int) (h_precond : solve_precond n k requests) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (k : Int) (requests : List Int) (cost : Int) (h_precond : solve_precond n k requests) : Prop :=
  ValidSolution n k requests cost

theorem solve_spec_satisfied (n : Int) (k : Int) (requests : List Int) (h_precond : solve_precond n k requests) :
    solve_postcond n k requests (solve n k requests h_precond) h_precond := by
  sorry
-- </vc-theorems>