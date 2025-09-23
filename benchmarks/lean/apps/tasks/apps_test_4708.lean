-- <vc-preamble>
-- Helper functions for string processing (axiomatized)
axiom SplitString : String → Char → List String
axiom IsValidInteger : String → Bool
axiom StringToInt : String → Int
axiom IntToString : Int → String

def ValidInput (input : String) : Prop :=
  let lines := SplitString input '\n'
  lines.length ≥ 4 ∧
  IsValidInteger (lines[0]!) ∧
  IsValidInteger (lines[1]!) ∧
  IsValidInteger (lines[2]!) ∧
  IsValidInteger (lines[3]!) ∧
  let N := StringToInt (lines[0]!)
  let K := StringToInt (lines[1]!)
  let X := StringToInt (lines[2]!)
  let Y := StringToInt (lines[3]!)
  1 ≤ N ∧ N ≤ 10000 ∧ 1 ≤ K ∧ K ≤ 10000 ∧ 1 ≤ Y ∧ Y < X ∧ X ≤ 10000

def ValidOutput (output input : String) : Prop :=
  let lines := SplitString input '\n'
  if lines.length ≥ 4 ∧ 
     IsValidInteger (lines[0]!) ∧
     IsValidInteger (lines[1]!) ∧
     IsValidInteger (lines[2]!) ∧
     IsValidInteger (lines[3]!) then
      let N := StringToInt (lines[0]!)
      let K := StringToInt (lines[1]!)
      let X := StringToInt (lines[2]!)
      let Y := StringToInt (lines[3]!)
      let expectedAns := if K < N then K * X + (N - K) * Y else N * X
      output = IntToString expectedAns ++ "\n"
  else
      output = ""

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0
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
  ValidOutput result input ∧
  (ValidInput input →
    let lines := SplitString input '\n'
    let N := StringToInt (lines[0]!)
    let K := StringToInt (lines[1]!)
    let X := StringToInt (lines[2]!)
    let Y := StringToInt (lines[3]!)
    (1 ≤ N ∧ N ≤ 10000 ∧ 1 ≤ K ∧ K ≤ 10000 ∧ 1 ≤ Y ∧ Y < X ∧ X ≤ 10000) →
    let expectedAns := if K < N then K * X + (N - K) * Y else N * X
    result = IntToString expectedAns ++ "\n")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>