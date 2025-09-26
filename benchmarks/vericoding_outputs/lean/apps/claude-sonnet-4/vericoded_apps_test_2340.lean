import Mathlib
-- <vc-preamble>
def ValidInput (h : Int) (n : Int) (platforms : List Int) : Prop :=
  h ≥ 1 ∧ n ≥ 1 ∧ platforms.length ≥ n ∧ n > 0 ∧ (platforms.get? 0).isSome ∧ platforms.get! 0 = h

def ValidCrystalCount (crystals : Int) (n : Int) : Prop :=
  crystals ≥ 0 ∧ crystals ≤ n - 1

def SimulatePositionUpTo (h : Int) (arr : List Int) (upTo : Nat) : Int :=
  match upTo with
  | 0 => h
  | upTo' + 1 =>
    let prevPos := SimulatePositionUpTo h arr upTo'
    let arrUpTo := arr.get? (upTo' + 1)
    let arrNext := arr.get? (upTo' + 2)
    match arrUpTo with
    | none => prevPos
    | some val =>
      if prevPos = val then prevPos
      else 
        match arrNext with
        | some nextVal => if nextVal = val - 1 then val - 1 else prevPos
        | none => prevPos

def CountCrystalsNeededUpTo (h : Int) (arr : List Int) (upTo : Nat) : Int :=
  match upTo with
  | 0 => 0
  | upTo' + 1 =>
    let curPos := SimulatePositionUpTo h arr upTo'
    let prevCrystals := CountCrystalsNeededUpTo h arr upTo'
    let arrUpTo := arr.get? (upTo' + 1)
    let arrNext := arr.get? (upTo' + 2)
    match arrUpTo with
    | none => prevCrystals
    | some val =>
      if curPos = val then prevCrystals
      else
        match arrNext with
        | some nextVal => if nextVal = val - 1 then prevCrystals else prevCrystals + 1
        | none => prevCrystals + 1

def CountCrystalsNeeded (h : Int) (platforms : List Int) : Int :=
  if platforms.length = 1 then 0
  else CountCrystalsNeededUpTo h (platforms ++ [0]) (platforms.length - 1)

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Parse input string to extract height and platform list
def parseInput (input : String) : Int × List Int :=
  let lines := input.splitOn "\n"
  let firstLine := lines[0]? |>.getD ""
  let parts := firstLine.splitOn " "
  let h := parts[0]? |>.getD "0" |>.toInt?
  let n := parts[1]? |>.getD "0" |>.toInt?
  let secondLine := lines[1]? |>.getD ""
  let platformStrs := secondLine.splitOn " "
  let platforms := platformStrs.map (fun s => s.toInt?.getD 0)
  (h.getD 1, platforms)
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  let (h, platforms) := parseInput input
  let crystalsNeeded := CountCrystalsNeeded h platforms
  toString crystalsNeeded
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result.length ≥ 0

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  unfold solve_postcond solve
  simp only [parseInput]
  -- String.length is always non-negative
  exact Nat.zero_le _
-- </vc-theorems>
