-- <vc-preamble>
def ValidInput (n k : Int) (L : List Int) : Prop :=
  n ≥ 1 ∧ k ≥ 1 ∧ L.length = n ∧ k ≤ n * (n + 1) / 2

def TotalIdentifiersAfterRobot (i : Int) : Int :=
  i * (i + 1) / 2

def CorrectResult (n k : Int) (L : List Int) (result : Int) : Prop :=
  ∃ i, 1 ≤ i ∧ i ≤ n ∧ 
    TotalIdentifiersAfterRobot (i - 1) < k ∧ k ≤ TotalIdentifiersAfterRobot i ∧
    result = L.get! (k - TotalIdentifiersAfterRobot (i - 1) - 1).natAbs

@[reducible, simp]
def solve_precond (n k : Int) (L : List Int) : Prop :=
  ValidInput n k L
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (L : List Int) (h_precond : solve_precond n k L) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (L : List Int) (result : Int) (h_precond : solve_precond n k L) : Prop :=
  CorrectResult n k L result

theorem solve_spec_satisfied (n k : Int) (L : List Int) (h_precond : solve_precond n k L) :
    solve_postcond n k L (solve n k L h_precond) h_precond := by
  sorry
-- </vc-theorems>