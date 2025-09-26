import Mathlib
-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0

def ValidTestCase (x1 y1 x2 y2 : Int) : Prop :=
  1 ≤ x1 ∧ x1 ≤ x2 ∧ 1 ≤ y1 ∧ y1 ≤ y2

def CountDifferentSums (x1 y1 x2 y2 : Int) (h : ValidTestCase x1 y1 x2 y2) : Int :=
  (x2 - x1) * (y2 - y1) + 1

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
instance (x1 y1 x2 y2 : Int) : Decidable (ValidTestCase x1 y1 x2 y2) := 
  inferInstanceAs (Decidable (1 ≤ x1 ∧ x1 ≤ x2 ∧ 1 ≤ y1 ∧ y1 ≤ y2))

-- LLM HELPER
def parseTestCase (line : String) : Option (Int × Int × Int × Int) :=
  let parts := line.splitOn " "
  if parts.length = 4 then
    match parts[0]?.bind String.toInt?, parts[1]?.bind String.toInt?,
          parts[2]?.bind String.toInt?, parts[3]?.bind String.toInt? with
    | some x1, some y1, some x2, some y2 => some (x1, y1, x2, y2)
    | _, _, _, _ => none
  else
    none

-- LLM HELPER
def processTestCases (lines : List String) : String :=
  lines.map (fun line =>
    match parseTestCase line with
    | some (x1, y1, x2, y2) =>
      if h : ValidTestCase x1 y1 x2 y2 then
        toString (CountDifferentSums x1 y1 x2 y2 h)
      else
        "0"  -- Invalid test case
    | none => "0"  -- Parse error
  ) |> String.intercalate "\n"
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  let lines := input.splitOn "\n" |>.filter (·.length > 0)
  let n := lines.head?.bind String.toNat? |>.getD 0
  if n > 0 ∧ n ≤ lines.length - 1 then
    let testCases := lines.tail.take n
    processTestCases testCases
  else
    ""
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (output : String) (h_precond : solve_precond input) : Prop :=
  output.length ≥ 0

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  unfold solve_postcond solve
  simp only [ge_iff_le]
  -- The output is either empty or contains processed test cases
  -- In both cases, the length is ≥ 0
  apply Nat.zero_le
-- </vc-theorems>
