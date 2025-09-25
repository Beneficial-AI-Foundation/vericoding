-- <vc-preamble>
def SplitLines (input : String) : List String := 
  input.splitOn "\n"

def ParseInt (s : String) : Int := 
  s.toInt?.getD 0

def ParseIntArray (s : String) : List Int := 
  (s.splitOn " ").map ParseInt

def ListSum (nums : List Int) : Int := nums.sum

def IsValidInput (input : String) : Prop :=
  let lines := SplitLines input
  lines.length ≥ 3 ∧ 
  ParseInt (lines[0]!) > 0 ∧
  (ParseIntArray (lines[1]!)).length = ParseInt (lines[0]!) ∧
  (ParseIntArray (lines[2]!)).length = ParseInt (lines[0]!)

def GetInitialSum (input : String) : Int :=
  let lines := SplitLines input
  ListSum (ParseIntArray (lines[1]!))

def GetTargetSum (input : String) : Int :=
  let lines := SplitLines input
  ListSum (ParseIntArray (lines[2]!))

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  True
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
  (result = "Yes" ∨ result = "No") ∧
  (IsValidInput input → 
      (result = "Yes" ↔ GetInitialSum input ≥ GetTargetSum input)) ∧
  (¬IsValidInput input → result = "No")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>