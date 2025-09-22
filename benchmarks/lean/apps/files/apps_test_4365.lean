-- <vc-preamble>
def ValidInput (K : Int) : Prop :=
  2 ≤ K ∧ K ≤ 100

def CountOddNumbers (K : Int) : Int :=
  (K + 1) / 2

def CountEvenNumbers (K : Int) : Int :=
  K / 2

def ExpectedResult (K : Int) : Int :=
  CountOddNumbers K * CountEvenNumbers K

def CorrectResult (K : Int) (result : Int) : Prop :=
  result = ExpectedResult K

@[reducible, simp]
def solve_precond (K : Int) : Prop :=
  ValidInput K
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (K : Int) (h_precond : solve_precond K) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (K : Int) (result : Int) (h_precond : solve_precond K) : Prop :=
  CorrectResult K result ∧ result ≥ 0

theorem solve_spec_satisfied (K : Int) (h_precond : solve_precond K) :
    solve_postcond K (solve K h_precond) h_precond := by
  sorry
-- </vc-theorems>