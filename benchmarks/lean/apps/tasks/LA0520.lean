-- <vc-preamble>
def ValidInput (n a b : Int) : Prop :=
  1 ≤ n ∧ n ≤ 20 ∧ 1 ≤ a ∧ a ≤ 50 ∧ 1 ≤ b ∧ b ≤ 50

def TrainCost (n a : Int) : Int :=
  n * a

def MinimumCost (n a b : Int) : Int :=
  let trainCost := TrainCost n a
  if trainCost < b then trainCost else b

-- String helper functions (axiomatized)
axiom SplitString : String → Char → List String
axiom IsValidInteger : String → Bool
axiom StringToInt : String → Int
axiom IntToString : Int → String

def CorrectResult (input result : String) : Prop :=
  let lines := SplitString input '\n'
  if lines.length > 0 then
    let parts := SplitString lines[0]! ' '
    if parts.length ≥ 3 ∧ IsValidInteger parts[0]! ∧ IsValidInteger parts[1]! ∧ IsValidInteger parts[2]! then
      let n := StringToInt parts[0]!
      let a := StringToInt parts[1]!
      let b := StringToInt parts[2]!
      ValidInput n a b → result = IntToString (MinimumCost n a b) ++ "\n"
    else
      result = ""
  else
    result = ""

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
  CorrectResult input result

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>