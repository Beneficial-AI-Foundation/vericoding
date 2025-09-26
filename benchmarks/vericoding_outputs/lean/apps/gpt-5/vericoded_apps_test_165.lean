import Mathlib
-- <vc-preamble>
def Max3 (a b c : Int) : Int :=
  if a ≥ b ∧ a ≥ c then a
  else if b ≥ c then b
  else c

def StringToInt (s : String) : Int := 0

def IntToString (n : Int) : String := ""

def TrimNewline (s : String) : String := s

def SplitSpaces (s : String) : List String := []

def CalculateMissedMeals (input : String) : Int :=
  let parts := SplitSpaces (TrimNewline input)
  if parts.length ≥ 3 then
    let a := StringToInt parts[0]!
    let b := StringToInt parts[1]!
    let c := StringToInt parts[2]!
    let maxVal := Max3 a b c
    let threshold := maxVal - 1
    (if a < threshold then threshold - a else 0) +
    (if b < threshold then threshold - b else 0) +
    (if c < threshold then threshold - c else 0)
  else 0

def ValidInput (input : String) : Prop := input.length > 0

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem solve_precond_iff (input : String) : solve_precond input ↔ ValidInput input := Iff.rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  IntToString (CalculateMissedMeals input)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result = IntToString (CalculateMissedMeals input)

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  rfl
-- </vc-theorems>
