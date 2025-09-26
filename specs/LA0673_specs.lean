-- <vc-preamble>
def ValidInput (dateStr : String) : Prop :=
  dateStr.length = 10 ∧ dateStr.take 4 = "2017"

def ValidOutput (input output : String) : Prop :=
  input.length ≥ 4 → 
  (output = "2018" ++ input.drop 4 ∧
   output.length = 10 ∧
   output.take 4 = "2018" ∧
   output.drop 4 = input.drop 4)

@[reducible, simp]
def solve_precond (dateStr : String) : Prop :=
  ValidInput dateStr
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (dateStr : String) (h_precond : solve_precond dateStr) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (dateStr : String) (result : String) (h_precond : solve_precond dateStr) : Prop :=
  ValidOutput dateStr result

theorem solve_spec_satisfied (dateStr : String) (h_precond : solve_precond dateStr) :
    solve_postcond dateStr (solve dateStr h_precond) h_precond := by
  sorry
-- </vc-theorems>