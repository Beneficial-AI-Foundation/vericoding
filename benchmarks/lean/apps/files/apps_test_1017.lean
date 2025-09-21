-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  n ≥ 1

def MaxDistributions (n : Int) (h : ValidInput n) : Int :=
  if n % 3 = 0 then 2 * (n / 3) else 2 * (n / 3) + 1

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
  result ≥ 1 ∧ result = MaxDistributions n h_precond

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>