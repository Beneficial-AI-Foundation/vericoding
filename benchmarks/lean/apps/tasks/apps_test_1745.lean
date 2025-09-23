-- <vc-preamble>
@[reducible, simp]
def ValidInput (input : String) : Prop :=
  input.length > 0 ∧ input.toList.getLast? = some '\n'

@[reducible, simp]
def ValidOutput (output : String) : Prop :=
  output.length > 0 ∧ output.toList.getLast? = some '\n'

def SplitLines (s : String) : List String :=
  s.splitOn "\n"

def ParseGrid (input : String) : (List (List Char) × Int × Int) :=
  let lines := SplitLines input
  if lines.length = 0 then ([], 0, 0)
  else
    let grid := lines.map (fun line => line.toList)
    let rows := grid.length
    let cols := if rows > 0 then grid[0]!.length else 0
    (grid, rows, cols)

def FindNewline (s : String) (start : Nat) : Int :=
  let chars := s.toList
  let rec helper (i : Nat) : Int :=
    if i >= chars.length then -1
    else if chars[i]! = '\n' then i
    else helper (i + 1)
  termination_by chars.length - i
  helper start

@[reducible, simp]
def IsValidGrid (grid : List (List Char)) (rows : Int) (cols : Int) : Prop :=
  grid.length = rows.natAbs ∧
  rows ≥ 0 ∧ cols ≥ 0 ∧
  (∀ i, 0 ≤ i ∧ i < rows → grid[i.natAbs]!.length = cols.natAbs) ∧
  (∀ i j, 0 ≤ i ∧ i < rows ∧ 0 ≤ j ∧ j < cols → 
    let cell := grid[i.natAbs]![j.natAbs]!
    cell = '.' ∨ cell = '#')

@[reducible, simp]
def IsBoundaryCell (i j rows cols : Int) : Prop :=
  rows > 0 ∧ cols > 0 ∧
  (i = 0 ∨ i = rows - 1 ∨ j = 0 ∨ j = cols - 1)

@[reducible, simp]
def IsCornerCell (i j rows cols : Int) : Prop :=
  rows > 0 ∧ cols > 0 ∧
  ((i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = cols - 1) ∨
   (i = rows - 1 ∧ j = 0) ∨ (i = rows - 1 ∧ j = cols - 1))

def CountValidPipes (_ : List (List Char)) (_ : Int) (_ : Int) : Int :=
  0

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (_ : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (_ : solve_precond input) : Prop :=
  ValidOutput result

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>