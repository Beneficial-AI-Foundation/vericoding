import Mathlib
-- <vc-preamble>
def ValidInput (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧
  (stdin_input.get ⟨stdin_input.length - 1⟩ = '\n' ∨ ¬('\n' ∈ stdin_input.toList))

def ValidResult (result : String) : Prop :=
  result = "BitAryo" ∨ result = "BitLGM"

-- Helper functions (assumed to exist)
axiom splitLines : String → List String
axiom parseInt : String → Int
axiom parseInts : String → List Int
axiom xorSequence : List Int → Int
noncomputable axiom goldenRatioRelation : List Int → Bool

noncomputable def GameResult (stdin_input : String) : String :=
  let lines := splitLines stdin_input
  if lines.length ≥ 1 then
    let n := parseInt (lines[0]!)
    if n = 3 ∧ lines.length ≥ 2 then
      let values := parseInts (lines[1]!)
      if values.length = 3 then
        let xorResult := xorSequence values
        if xorResult = 0 then "BitAryo" else "BitLGM"
      else "BitLGM"
    else if n = 2 ∧ lines.length ≥ 2 then
      let values := parseInts (lines[1]!)
      if values.length = 2 ∧ values[0]! ≥ 0 ∧ values[1]! ≥ 0 then
        let sortedValues := if values[0]! ≤ values[1]! then values else [values[1]!, values[0]!]
        if goldenRatioRelation sortedValues then "BitAryo" else "BitLGM"
      else "BitLGM"
    else if lines.length ≥ 2 then
      let value := parseInt (lines[1]!)
      if value = 0 then "BitAryo" else "BitLGM"
    else "BitLGM"
  else "BitLGM"

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma gameResult_valid (stdin_input : String) : ValidResult (GameResult stdin_input) := by
  unfold ValidResult GameResult
  dsimp
  split_ifs <;> simp [ValidResult]
-- </vc-helpers>

-- <vc-definitions>
noncomputable def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  GameResult stdin_input
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (_ : solve_precond stdin_input) : Prop :=
  ValidResult result ∧ result = GameResult stdin_input

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · exact gameResult_valid stdin_input
  · rfl
-- </vc-theorems>
