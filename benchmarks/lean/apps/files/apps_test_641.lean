-- <vc-preamble>
-- Helper function for splitting strings on spaces (axiomatized)
noncomputable axiom SplitOnSpace : String → List String

noncomputable def ValidInput (input : String) : Prop :=
  input.length > 0 ∧
  let trimmed := if input.length > 0 ∧ input.back = '\n' 
                 then input.dropRight 1 
                 else input
  let parts := SplitOnSpace trimmed
  parts.length ≥ 1

noncomputable def GetExpectedResult (input : String) : String :=
  let trimmed := if input.length > 0 ∧ input.back = '\n' 
                 then input.dropRight 1 
                 else input
  let parts := SplitOnSpace trimmed
  if parts.getLast! = "month" then
    if parts.head! = "31" then "7\n"
    else if parts.head! = "30" then "11\n"
    else "12\n"
  else
    if parts.head! = "5" ∨ parts.head! = "6" then "53\n"
    else "52\n"

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
noncomputable def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result = GetExpectedResult input

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>