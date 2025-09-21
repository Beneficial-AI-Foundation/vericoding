-- <vc-preamble>
def ValidInput (N : Int) : Prop :=
  1 ≤ N ∧ N ≤ 100

def countDivisorsWith75Factors (N : Int) (h : ValidInput N) : Int :=
  0

def ValidOutput (result : Int) : Prop :=
  result ≥ 0

@[reducible, simp]
def solve_precond (N : Int) : Prop :=
  ValidInput N
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (h_precond : solve_precond N) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (result : Int) (h_precond : solve_precond N) : Prop :=
  ValidOutput result

theorem solve_spec_satisfied (N : Int) (h_precond : solve_precond N) :
    solve_postcond N (solve N h_precond) h_precond := by
  sorry
-- </vc-theorems>