-- <vc-preamble>
def ValidInput (n m : Int) : Prop :=
  2 ≤ n ∧ n ≤ 100 ∧ 2 ≤ m ∧ m ≤ 100

def CountBlocks (n m : Int) : Int :=
  (n - 1) * (m - 1)

def CorrectOutput (n m blocks : Int) : Prop :=
  ValidInput n m ∧ blocks = CountBlocks n m

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
def solve_postcond (n m : Int) (blocks : Int) (h_precond : solve_precond n m) : Prop :=
  CorrectOutput n m blocks ∧ blocks ≥ 1

theorem solve_spec_satisfied (n m : Int) (h_precond : solve_precond n m) :
    solve_postcond n m (solve n m h_precond) h_precond := by
  sorry
-- </vc-theorems>