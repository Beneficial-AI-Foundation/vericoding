-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  100 ≤ n ∧ n ≤ 999

def IntToString (n : Int) : String :=
  toString n

def ValidOutput (n : Int) (result : String) (h_valid : ValidInput n) : Prop :=
  result.length = 6 ∧ result.take 3 = "ABC" ∧ result.drop 3 = IntToString n

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : String) (h_precond : solve_precond n) : Prop :=
  ValidOutput n result h_precond

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>