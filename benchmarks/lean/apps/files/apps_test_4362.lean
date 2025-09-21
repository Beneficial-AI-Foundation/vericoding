-- <vc-preamble>
def IsLowercaseLetter (c : Char) : Prop :=
  'a' ≤ c ∧ c ≤ 'z'

def AllLowercase (s : String) : Prop :=
  s.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < s.length → IsLowercaseLetter (s.data.get! i)

def ValidOutput (result : String) : Prop :=
  result = "A" ∨ result = "a"

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (_ : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (_ : solve_precond input) : Prop :=
  ValidOutput result ∧ 
  (AllLowercase input → result = "a") ∧
  ((input.length = 0 ∨ ¬AllLowercase input) → result = "A")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>