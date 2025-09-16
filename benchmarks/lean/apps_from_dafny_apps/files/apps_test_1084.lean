-- <vc-preamble>
def ValidInput (input : String) : Bool :=
  input.length > 0 && input.contains '\n'

def SplitLinesHelper (input : String) (start : Nat) (acc : List String) : List String :=
  sorry

def SplitLines (input : String) : List String :=
  if input.length > 0 then
    SplitLinesHelper input 0 []
  else
    []

def SplitOnSpace (line : String) : List String :=
  sorry

def StringToInt (s : String) : Int :=
  sorry

def ParseDimensions (line : String) : (Int × Int) :=
  let parts := SplitOnSpace line
  if parts.length ≥ 2 then
    (StringToInt parts[0]!, StringToInt parts[1]!)
  else
    (0, 0)

def ValidGrid (gridLines : List String) (m : Int) : Bool :=
  (gridLines.all (fun row => row.length = m.natAbs)) &&
  (gridLines.all (fun row => 
    row.data.all (fun c => c = '.' || c = '#')))

def GetRowPattern (row : String) (m : Int) : List Int :=
  if row.length = m.natAbs then
    List.range m.natAbs |>.filter (fun j => if h : j < row.length then row.data[j] = '#' else false) |>.map Int.ofNat
  else
    []

def CanBeConstructedByOperations (input : String) : Bool :=
  if ValidInput input then
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
            col < gridLines[i]!.length && (if h : col < gridLines[i]!.length then gridLines[i]!.data[col] = '#' else false))
          rowsWithThisCol.length ≤ 1 ||
          (rowsWithThisCol.all (fun i => rowsWithThisCol.all (fun j =>
            GetRowPattern gridLines[i]! m = GetRowPattern gridLines[j]! m))))
  else
    false

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input = true
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (_ : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (_ : solve_precond stdin_input) : Prop :=
  (result = "Yes\n" ∨ result = "No\n") ∧
  result.length > 0 ∧
  (result = "Yes\n" ↔ CanBeConstructedByOperations stdin_input = true)

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>
