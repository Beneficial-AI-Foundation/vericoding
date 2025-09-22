-- <vc-preamble>
partial def clean_input (s : String) : String :=
  if s.length = 0 then s
  else 
    let lastChar := s.data[s.length - 1]?
    if lastChar = some '\n' ∨ lastChar = some '\r' ∨ lastChar = some ' ' then
      clean_input (String.mk (s.data.take (s.length - 1)))
    else s

def contains_digit_nine (s : String) : Prop :=
  ∃ i, i < s.length ∧ s.data[i]? = some '9'

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  (result = "Yes\n" ∨ result = "No\n") ∧
  (result = "Yes\n" ↔ contains_digit_nine (clean_input stdin_input)) ∧
  (result = "No\n" ↔ ¬contains_digit_nine (clean_input stdin_input))

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>