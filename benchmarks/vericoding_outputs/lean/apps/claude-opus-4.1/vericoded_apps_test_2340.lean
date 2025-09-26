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
-- LLM HELPER
def parseInput (input : String) : Option (Int × Int × List Int) :=
  let lines := input.trim.splitOn "\n"
  match lines with
  | [line1, line2] =>
    let nums1 := line1.trim.splitOn " "
    let nums2 := line2.trim.splitOn " "
    match nums1 with
    | [hStr, nStr] =>
      match hStr.toInt?, nStr.toInt? with
      | some h, some n =>
        let platforms := nums2.filterMap (·.toInt?)
        if platforms.length = n.toNat then
          some (h, n, platforms)
        else
          none
      | _, _ => none
    | _ => none
  | _ => none

-- LLM HELPER
def checkValidInput (h : Int) (n : Int) (platforms : List Int) : Bool :=
  h ≥ 1 && n ≥ 1 && platforms.length ≥ n && n > 0 && 
  match platforms[0]? with
  | none => false
  | some val => val = h
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  let parsed := parseInput input
match parsed with
| none => "0"
| some (h, n, platforms) =>
  if checkValidInput h n platforms then
    let crystalsNeeded := CountCrystalsNeeded h platforms
    s!"{crystalsNeeded}"
  else
    "0"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result.length ≥ 0

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  unfold solve_postcond
  unfold solve
  -- We need to simplify the have expression first
  simp only []
  -- Now we can split on the match
  cases parseInput input with
  | none => 
    -- Case: parseInput returns none
    simp only []
    decide
  | some triple =>
    -- Case: parseInput returns some value
    obtain ⟨h, n, platforms⟩ := triple
    simp only []
    -- Split on the if condition
    by_cases hc : checkValidInput h n platforms
    · -- Case: checkValidInput is true
      simp only [if_pos hc]
      -- The string interpolation produces a non-empty string
      have : s!"{CountCrystalsNeeded h platforms}".length ≥ 0 := by
        apply Nat.zero_le
      exact this
    · -- Case: checkValidInput is false  
      simp only [if_neg hc]
      decide
-- </vc-theorems>
