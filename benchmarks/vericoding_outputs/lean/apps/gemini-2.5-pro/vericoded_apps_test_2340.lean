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
def parseInput (input : String) : Option (Int × Int × (List Int)) :=
  match (input.splitOn " ").filterMap String.toInt? with
  | h :: n :: platforms => some (h, n, platforms)
  | _ => none

-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
    match parseInput input with
  | some (h, n, platforms) =>
    if n > 0 then
      let platforms_n := platforms.take n.toNat
      ToString.toString (CountCrystalsNeeded h platforms_n)
    else
      "0"
  | none => "0"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result.length ≥ 0

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
    simp [solve_postcond]
-- </vc-theorems>
