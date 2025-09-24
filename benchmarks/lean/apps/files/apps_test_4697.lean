-- <vc-preamble>
def ValidInput (n m : Int) : Prop :=
  n ≥ 0 ∧ m ≥ 0

def MaxSccGroups (n m : Int) (h : ValidInput n m) : Int :=
  let directGroups := if n < m / 2 then n else m / 2
  let remainingCPieces := m - directGroups * 2
  let additionalGroups := remainingCPieces / 4
  directGroups + additionalGroups

@[reducible, simp]
def solve_precond (n m : Int) : Prop :=
  ValidInput n m
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (h_precond : solve_precond n m) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (result : Int) (h_precond : solve_precond n m) : Prop :=
  result ≥ 0 ∧ result = MaxSccGroups n m h_precond

theorem solve_spec_satisfied (n m : Int) (h_precond : solve_precond n m) :
    solve_postcond n m (solve n m h_precond) h_precond := by
  sorry
-- </vc-theorems>