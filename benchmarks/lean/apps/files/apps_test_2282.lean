-- <vc-preamble>
-- Helper functions (axiomatized for now)
noncomputable axiom split : String → Char → List String
axiom isValidInteger : String → Bool
axiom parseInteger : String → Int
axiom intToString : Int → String

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧ ∃ i, 0 ≤ i ∧ i < input.length ∧ input.data[i]! = '\n'

def ValidCommandInput (input : String) : Prop :=
  let lines := split input '\n'
  lines.length ≥ 2 ∧ lines[0]! ≠ "" ∧ isValidInteger lines[0]!

noncomputable def ExtractN (input : String) : Int :=
  let lines := split input '\n'
  parseInteger lines[0]!

def CorrectOutput (input : String) (result : String) : Prop :=
  ValidCommandInput input → 
    result = intToString (ExtractN input + 1) ++ "\n"

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
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
  CorrectOutput input result ∧ (¬ValidCommandInput input → result = "")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>