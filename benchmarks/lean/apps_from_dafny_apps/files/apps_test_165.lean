-- <vc-preamble>
-- <vc-preamble>
def Max3 (a b c : Int) : Int :=
  if a ≥ b ∧ a ≥ c then a
  else if b ≥ c then b
  else c

-- Placeholder functions for string operations
def SplitSpaces (s : String) : List String := sorry
def TrimNewline (s : String) : String := sorry
def StringToInt (s : String) : Int := sorry
def IntToString (n : Int) : String := sorry

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

def ValidInput (input : String) : Prop :=
  input.length > 0

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
  result = IntToString (CalculateMissedMeals input)

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>
