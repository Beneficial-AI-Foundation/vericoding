-- <vc-preamble>
-- <vc-preamble>
def Split (s : String) (delimiter : Char) : List String :=
  sorry

def ParseInt (s : String) : Int :=
  sorry

def IntToString (n : Int) : String :=
  sorry

def ValidInput (input : String) : Prop :=
  let lines := Split input '\n'
  lines.length ≥ 2 ∧
  ParseInt (lines[0]!) ≥ 1 ∧
  let n := ParseInt (lines[0]!)
  let secondLineParts := Split (lines[1]!) ' '
  secondLineParts.length ≥ 2 ∧
  ParseInt (secondLineParts[0]!) ≥ 1 ∧
  ParseInt (secondLineParts[1]!) ≥ 0 ∧
  lines.length ≥ Int.natAbs (2 + n) ∧
  (∀ i, 0 ≤ i ∧ i < n → ParseInt (lines[Int.natAbs (2 + i)]!) ≥ 1)

def SumEatenForParticipants (lines : List String) (d : Int) (count : Int) : Int :=
  sorry

def ComputeExpectedResult (input : String) : String :=
  let lines := Split input '\n'
  let n := ParseInt (lines[0]!)
  let secondLineParts := Split (lines[1]!) ' '
  let d := ParseInt (secondLineParts[0]!)
  let x := ParseInt (secondLineParts[1]!)
  let totalEaten := SumEatenForParticipants lines d n
  IntToString (x + totalEaten)

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ ValidInput input
-- </vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result.length > 0 ∧ result = ComputeExpectedResult input

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>
