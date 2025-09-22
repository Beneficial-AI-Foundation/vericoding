-- <vc-preamble>
axiom ContainsRequiredNewlines : String → Prop
axiom EndsWithNewlineOrCanAppend : String → Prop
axiom HasValidStructure : String → Prop
axiom AllGridCharactersValid : String → Prop
axiom HasExactlyRequiredLines : String → Prop
axiom GridContainsOnlyValidChars : String → Prop
axiom CoordinatesWithinBounds : String → Prop
axiom CountSurroundingIntactIce : List (List Char) → Int → Int → Int
axiom CanReachTargetWithBFS : List (List Char) → Int → Int → Int → Int → Prop
axiom IsAdjacent : Int → Int → Int → Int → Prop

def ParseDimensions (stdin_input : String) : Int × Int :=
  (1, 1)

def ParseGrid (stdin_input : String) : List (List Char) :=
  [['X']]

def ParseCoordinates (stdin_input : String) : Int × Int × Int × Int :=
  (1, 1, 1, 1)

def ValidGridIndex (grid : List (List Char)) (r c : Int) : Prop :=
  0 ≤ r ∧ r < grid.length ∧ 0 ≤ c ∧ c < (grid[r.natAbs]!).length

def ValidInputFormat (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧
  stdin_input.length ≥ 7 ∧
  ContainsRequiredNewlines stdin_input ∧
  EndsWithNewlineOrCanAppend stdin_input ∧
  HasValidStructure stdin_input ∧
  AllGridCharactersValid stdin_input ∧
  HasExactlyRequiredLines stdin_input

def ValidGridBounds (stdin_input : String) : Prop :=
  let parsed := ParseDimensions stdin_input
  parsed.1 ≥ 1 ∧ parsed.1 ≤ 500 ∧ parsed.2 ≥ 1 ∧ parsed.2 ≤ 500

def ValidCoordinates (stdin_input : String) : Prop :=
  let dims := ParseDimensions stdin_input
  let coords := ParseCoordinates stdin_input
  coords.1 ≥ 1 ∧ coords.1 ≤ dims.1 ∧ coords.2.1 ≥ 1 ∧ coords.2.1 ≤ dims.2 ∧
  coords.2.2.1 ≥ 1 ∧ coords.2.2.1 ≤ dims.1 ∧ coords.2.2.2 ≥ 1 ∧ coords.2.2.2 ≤ dims.2

def StartingCellIsCracked (stdin_input : String) : Prop :=
  let grid := ParseGrid stdin_input
  let coords := ParseCoordinates stdin_input
  ValidGridIndex grid (coords.1-1) (coords.2.1-1) ∧
  (grid[(coords.1-1).natAbs]!)[(coords.2.1-1).natAbs]! = 'X'

def WellFormedInput (stdin_input : String) : Prop :=
  ValidInputFormat stdin_input ∧
  ValidGridBounds stdin_input ∧
  ValidCoordinates stdin_input ∧
  StartingCellIsCracked stdin_input ∧
  GridContainsOnlyValidChars stdin_input ∧
  CoordinatesWithinBounds stdin_input

def CanSolveIceMaze (stdin_input : String) : Prop :=
  let grid := ParseGrid stdin_input
  let coords := ParseCoordinates stdin_input
  let r1 := coords.1-1
  let c1 := coords.2.1-1
  let r2 := coords.2.2.1-1
  let c2 := coords.2.2.2-1
  let targetIsCracked := (grid[r2.natAbs]!)[c2.natAbs]! = 'X'
  let surroundingDots := CountSurroundingIntactIce grid r2 c2
  if targetIsCracked then
    if r1 = r2 ∧ c1 = c2 then
      surroundingDots ≥ 1
    else
      CanReachTargetWithBFS grid r1 c1 r2 c2
  else
    if surroundingDots ≥ 2 then
      CanReachTargetWithBFS grid r1 c1 r2 c2
    else if surroundingDots = 0 then
      False
    else
      IsAdjacent (r1+1) (c1+1) (r2+1) (c2+1)

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧
  ValidInputFormat stdin_input ∧
  ValidGridBounds stdin_input ∧
  ValidCoordinates stdin_input ∧
  StartingCellIsCracked stdin_input ∧
  WellFormedInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  (result = "YES\n" ∨ result = "NO\n") ∧
  result.length > 0 ∧
  (result = "YES\n" ↔ CanSolveIceMaze stdin_input)

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>