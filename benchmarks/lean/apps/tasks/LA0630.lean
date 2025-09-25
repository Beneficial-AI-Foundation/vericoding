-- <vc-preamble>
def Split (s : String) (delimiter : Char) : List String :=
  s.split (· = delimiter)

def ParseInt (s : String) : Int :=
  s.toInt?.getD 0

def IntToString (n : Int) : String :=
  toString n

def ValidInput (input : String) : Prop :=
  let lines := Split input '\n'
  lines.length ≥ 2 ∧
  ParseInt (lines[0]!) ≥ 1 ∧
  let n := ParseInt (lines[0]!)
  let secondLineParts := Split (lines[1]!) ' '
  secondLineParts.length ≥ 2 ∧
  ParseInt (secondLineParts[0]!) ≥ 1 ∧
  ParseInt (secondLineParts[1]!) ≥ 0 ∧
  lines.length ≥ (2 + n.natAbs) ∧
  ∀ i, 0 ≤ i ∧ i < n → ParseInt (lines[(2 + i.natAbs)]!) ≥ 1

def SumEatenForParticipants (lines : List String) (d : Int) (count : Nat) : Int :=
  if count = 0 then 0
  else
    let a := ParseInt (lines[2 + count - 1]!)
    let eaten := if a > 0 then (d + a - 1) / a else 0
    eaten + SumEatenForParticipants lines d (count - 1)

def ComputeExpectedResult (input : String) : String :=
  let lines := Split input '\n'
  let n := ParseInt (lines[0]!)
  let secondLineParts := Split (lines[1]!) ' '
  let d := ParseInt (secondLineParts[0]!)
  let x := ParseInt (secondLineParts[1]!)
  let totalEaten := SumEatenForParticipants lines d n.natAbs
  IntToString (x + totalEaten)

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result.length > 0 ∧ result = ComputeExpectedResult input

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>