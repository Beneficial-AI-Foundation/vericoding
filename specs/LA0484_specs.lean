-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  1 ≤ n ∧ n ≤ 10000

def ValidChange (change : Int) : Prop :=
  0 ≤ change ∧ change ≤ 999

def CorrectChange (n : Int) (h : ValidInput n) : Int :=
  (1000 - n % 1000) % 1000

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
def solve_postcond (n : Int) (change : Int) (h_precond : solve_precond n) : Prop :=
  ValidChange change ∧ change = CorrectChange n h_precond

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>