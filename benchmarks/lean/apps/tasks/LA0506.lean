-- <vc-preamble>
-- Helper functions for string parsing and manipulation
axiom parse_lines : String → List String
axiom int_to_string : Int → String

noncomputable def is_valid_input (input: String) : Prop :=
  input.length > 0 ∧
  let lines := parse_lines input
  lines.length ≥ 2 ∧ lines[0]!.length = 3 ∧ lines[1]!.length = 3

def count_matches (s t: String) : Int :=
  (if s.data[0]! = t.data[0]! then 1 else 0) +
  (if s.data[1]! = t.data[1]! then 1 else 0) +
  (if s.data[2]! = t.data[2]! then 1 else 0)

noncomputable def count_matches_from_input (input: String) : Int :=
  let lines := parse_lines input
  count_matches lines[0]! lines[1]!

noncomputable def compute_result (input: String) : String :=
  let lines := parse_lines input
  if lines.length < 2 then "0\n"
  else if lines[0]!.length ≠ 3 ∨ lines[1]!.length ≠ 3 then "0\n"
  else int_to_string (count_matches lines[0]! lines[1]!) ++ "\n"

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
noncomputable def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
noncomputable def solve_postcond (input : String) (result: String) (h_precond : solve_precond input) : Prop :=
  result = compute_result input ∧
  result.length ≥ 2 ∧ 
  result.data[result.length - 1]! = '\n'

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>