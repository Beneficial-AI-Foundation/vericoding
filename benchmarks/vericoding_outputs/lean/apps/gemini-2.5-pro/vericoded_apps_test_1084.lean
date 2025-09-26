import Mathlib
-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0 ∧ '\n' ∈ input.toList

def SplitLinesHelper (_ : String) (_ : Nat) (_ : List String) : List String :=
  []

def SplitLines (input : String) : List String :=
  if input.length > 0 then SplitLinesHelper input 0 [] else []

def SplitOnSpace (_ : String) : List String :=
  []

def StringToInt (_ : String) : Int :=
  0

def ParseDimensions (line : String) : (Int × Int) :=
  let parts := SplitOnSpace line
  if parts.length ≥ 2 then
    (StringToInt parts[0]!, StringToInt parts[1]!)
  else
    (0, 0)

def ValidGrid (gridLines : List String) (m : Int) : Bool :=
  (gridLines.all (fun row => row.length = m.natAbs)) &&
  (gridLines.all (fun row => 
      row.toList.all (fun c => c = '.' || c = '#')))

def GetRowPattern (row : String) (m : Int) : List Nat :=
  List.range m.natAbs |>.filter (fun j => j < row.length && row.data[j]! = '#')

def CanBeConstructedByOperations (input : String) : Bool :=
  let lines := SplitLines input
  if lines.length < 2 then false
  else
    let firstLine := lines[0]!
    let gridLines := lines.drop 1
    let dimensions := ParseDimensions firstLine
    let n := dimensions.1
    let m := dimensions.2
    if n ≤ 0 || m ≤ 0 || gridLines.length ≠ n.natAbs then false
    else if !ValidGrid gridLines m then false
    else
      List.range m.natAbs |>.all (fun col =>
          let rowsWithThisCol := List.range n.natAbs |>.filter (fun i => 
            col < gridLines[i]!.length && gridLines[i]!.data[col]! = '#')
          rowsWithThisCol.length ≤ 1 ||
          rowsWithThisCol.all (fun i => 
            rowsWithThisCol.all (fun j =>
              GetRowPattern gridLines[i]! m = GetRowPattern gridLines[j]! m)))

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma CanBeConstructedByOperations_is_false (input : String) : CanBeConstructedByOperations input = false := by
  unfold CanBeConstructedByOperations
  unfold SplitLines SplitLinesHelper
  simp
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  if CanBeConstructedByOperations stdin_input then
    "Yes\n"
  else
    "No\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (_ : solve_precond stdin_input) : Prop :=
  (result = "Yes\n" ∨ result = "No\n") ∧
  result.length > 0 ∧
  (result = "Yes\n" ↔ CanBeConstructedByOperations stdin_input = true)

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  unfold solve solve_postcond
  rw [CanBeConstructedByOperations_is_false stdin_input]
  simp
  change 0 < 3
  exact Nat.zero_lt_succ 2
-- </vc-theorems>
