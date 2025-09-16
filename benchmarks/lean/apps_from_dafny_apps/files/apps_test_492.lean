-- <vc-preamble>
-- <vc-preamble>
def CharToPosSpec (c : String) : Int :=
  if c = "v" then 0
  else if c = ">" then 1
  else if c = "^" then 2
  else if c = "<" then 3
  else 0

def FindNewline (s : String) (start : Int) : Int :=
  sorry

def SplitLinesSpec (s : String) : List String :=
  sorry

def FindSpace (s : String) (start : Int) : Int :=
  sorry

def SplitBySpaceSpec (s : String) : List String :=
  sorry

def StringToIntHelper (s : String) (pos : Int) (acc : Int) (negative : Bool) : Int :=
  sorry

def StringToIntSpec (s : String) : Int :=
  StringToIntHelper s 0 0 false

def ValidInput (input : String) : Prop :=
  input.length > 0

def ValidOutput (result : String) : Prop :=
  result = "cw" ∨ result = "ccw" ∨ result = "undefined"

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  ValidOutput result ∧
  (input.length > 0 → (
    let lines := SplitLinesSpec input
    lines.length ≥ 2 → (
      let positions := SplitBySpaceSpec lines[0]!
      positions.length ≥ 2 → (
        let startChar := positions[0]!
        let endChar := positions[1]!
        let n := StringToIntSpec lines[1]!
        let startPos := CharToPosSpec startChar
        let endPos := CharToPosSpec endChar
        let ccw := (startPos + n) % 4 = endPos
        let cw := (startPos - n) % 4 = endPos
        (cw ∧ ¬ccw → result = "cw") ∧
        (ccw ∧ ¬cw → result = "ccw") ∧
        (¬(cw ∧ ¬ccw) ∧ ¬(ccw ∧ ¬cw) → result = "undefined")
      )
    )
  ))

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>
