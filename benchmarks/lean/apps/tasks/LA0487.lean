-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  1 ≤ n ∧ n ≤ 16

def FactTruthValues : List Int :=
  [1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0]

def ValidOutput (result : Int) : Prop :=
  result = 0 ∨ result = 1

def ExpectedOutput (n : Int) (h : ValidInput n) : Int :=
  FactTruthValues[n.natAbs - 1]!

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
  ValidOutput result ∧ result = ExpectedOutput n h_precond

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>