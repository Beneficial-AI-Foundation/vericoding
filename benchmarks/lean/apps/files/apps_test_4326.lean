-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  1 ≤ n ∧ n ≤ 1000

def MaxGroupsWithAtLeastThree (n : Int) (h : ValidInput n) : Int :=
  n / 3

def ValidSolution (n : Int) (result : Int) (h : ValidInput n) : Prop :=
  result = MaxGroupsWithAtLeastThree n h ∧
  result ≥ 0 ∧
  result ≤ n

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : Int) (h_precond : solve_precond n) : Prop :=
  ValidSolution n result h_precond

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>