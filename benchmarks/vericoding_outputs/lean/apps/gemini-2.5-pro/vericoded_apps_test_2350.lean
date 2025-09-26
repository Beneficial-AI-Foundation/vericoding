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
def parse_input (s : String) : Option (Int × Int × Int × Int) := 
  match (s.splitOn " ").mapM (·.toInt?) with
  | some [x1, y1, x2, y2] => some (x1, y1, x2, y2)
  | _ => none

-- LLM HELPER
instance (x1 y1 x2 y2 : Int) : Decidable (ValidTestCase x1 y1 x2 y2) := by
  unfold ValidTestCase
  infer_instance

-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  match parse_input input with
  | some (x1, y1, x2, y2) =>
    if h : ValidTestCase x1 y1 x2 y2 then
      ToString.toString (CountDifferentSums x1 y1 x2 y2 h)
    else
      "0"
  | none => "0"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (output : String) (h_precond : solve_precond input) : Prop :=
  output.length ≥ 0

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  simp
-- </vc-theorems>
