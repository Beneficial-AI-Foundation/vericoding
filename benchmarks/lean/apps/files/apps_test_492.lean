-- <vc-preamble>
def CharToPosSpec (c : String) : Int :=
  if c == "v" then 0
  else if c == ">" then 1
  else if c == "^" then 2
  else if c == "<" then 3
  else 0

partial def FindNewline (s : String) (start : Nat) : Nat :=
  if start >= s.length then s.length
  else if s.data[start]! == '\n' then start
  else FindNewline s (start + 1)

partial def SplitLinesSpec (s : String) : List String :=
  if s.length == 0 then []
  else
    let i := FindNewline s 0
    if i == s.length then [s]
    else [s.take i] ++ SplitLinesSpec (s.drop (i+1))

partial def FindSpace (s : String) (start : Nat) : Nat :=
  if start >= s.length then s.length
  else if s.data[start]! == ' ' then start
  else FindSpace s (start + 1)

partial def SplitBySpaceSpec (s : String) : List String :=
  if s.length == 0 then []
  else
    let i := FindSpace s 0
    if i == s.length then [s]
    else [s.take i] ++ SplitBySpaceSpec (s.drop (i+1))

partial def StringToIntHelper (s : String) (pos : Nat) (acc : Int) (negative : Bool) : Int :=
  if pos >= s.length then (if negative then -acc else acc)
  else if pos == 0 && s.data[pos]! == '-' then StringToIntHelper s (pos + 1) acc true
  else if '0' ≤ s.data[pos]! && s.data[pos]! ≤ '9' then 
    StringToIntHelper s (pos + 1) (acc * 10 + (s.data[pos]!).toNat - '0'.toNat) negative
  else StringToIntHelper s (pos + 1) acc negative

def StringToIntSpec (s : String) : Int :=
  StringToIntHelper s 0 0 false

def ValidInput (input : String) : Prop :=
  input.length > 0

def ValidOutput (result : String) : Prop :=
  result == "cw" ∨ result == "ccw" ∨ result == "undefined"

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