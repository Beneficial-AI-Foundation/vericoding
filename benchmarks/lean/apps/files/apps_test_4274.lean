-- <vc-preamble>
-- Helper functions for string processing (axiomatized)
noncomputable axiom Split : String → Char → List String
noncomputable axiom StringToInt : String → Int

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧
  ∃ lines, lines = Split input '\n' ∧ lines.length > 0 ∧
  ∃ parts, parts = Split lines[0]! ' ' ∧ parts.length = 2 ∧
  ∃ n m, n = StringToInt parts[0]! ∧ 
         m = StringToInt parts[1]! ∧
         1 ≤ n ∧ n ≤ 100 ∧ 0 ≤ m ∧ m ≤ n

noncomputable def ExtractN (input : String) (h : ValidInput input) : Int :=
  let lines := Split input '\n'
  let parts := Split lines[0]! ' '
  StringToInt parts[0]!

noncomputable def ExtractM (input : String) (h : ValidInput input) : Int :=
  let lines := Split input '\n'
  let parts := Split lines[0]! ' '
  StringToInt parts[1]!

def CorrectOutput (input : String) (result : String) (h : ValidInput input) : Prop :=
  let n := ExtractN input h
  let m := ExtractM input h
  (n = m → result = "Yes") ∧ (n ≠ m → result = "No")

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
  CorrectOutput input result h_precond ∧ (result = "Yes" ∨ result = "No")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>