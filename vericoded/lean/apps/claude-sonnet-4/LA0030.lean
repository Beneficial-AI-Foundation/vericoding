import Mathlib
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
-- LLM HELPER: Make IsValidInput decidable for any input
instance decidableIsValidInput (input : String) : Decidable (IsValidInput input) := by
  unfold IsValidInput
  infer_instance
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  if h : IsValidInput input then
  if GetInitialSum input ≥ GetTargetSum input then "Yes" else "No"
else
  "No"
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
  unfold solve solve_postcond
  constructor
  · -- First goal: result = "Yes" ∨ result = "No"
    by_cases h_valid : IsValidInput input
    · by_cases h_sum : GetInitialSum input ≥ GetTargetSum input
      · simp [h_valid, h_sum]
      · simp [h_valid, h_sum]
    · simp [h_valid]
  constructor
  · -- Second goal: IsValidInput input → (result = "Yes" ↔ GetInitialSum input ≥ GetTargetSum input)
    intro h_valid
    by_cases h_sum : GetInitialSum input ≥ GetTargetSum input
    · simp [h_valid, h_sum]
    · simp [h_valid, h_sum]
  · -- Third goal: ¬IsValidInput input → result = "No" 
    intro h_invalid
    simp [h_invalid]
-- </vc-theorems>
