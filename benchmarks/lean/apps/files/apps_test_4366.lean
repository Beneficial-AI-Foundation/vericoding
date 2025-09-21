-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  ∃ A B, 0 ≤ A ∧ A ≤ 23 ∧ 0 ≤ B ∧ B ≤ 23 ∧ 
  (input = toString A ++ " " ++ toString B ++ "\n" ∨
   input = toString A ++ " " ++ toString B)

def ContestStartTime (A B : Int) : Int :=
  (A + B) % 24

def CorrectOutput (input result : String) (h_valid : ValidInput input) : Prop :=
  ∃ A B, 0 ≤ A ∧ A ≤ 23 ∧ 0 ≤ B ∧ B ≤ 23 ∧ 
  (input = toString A ++ " " ++ toString B ++ "\n" ∨
   input = toString A ++ " " ++ toString B) ∧
  result = toString (ContestStartTime A B) ++ "\n"

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  CorrectOutput input result (h_precond.2)

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>