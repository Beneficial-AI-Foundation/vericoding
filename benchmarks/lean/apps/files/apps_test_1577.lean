-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0 ∧ ∃ newlinePos, 0 ≤ newlinePos ∧ newlinePos < input.length ∧ input.data[newlinePos]! = '\n'

def IsValidInteger (s : String) : Prop :=
  s.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < s.length → s.data[i]! ≥ '0' ∧ s.data[i]! ≤ '9'

def IsValidGameString (s : String) : Prop :=
  ∀ i, 0 ≤ i ∧ i < s.length → s.data[i]! = 'A' ∨ s.data[i]! = 'D'

def StringToInt (s : String) : Int := 
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def SplitLines (input : String) : List String := 
  input.splitOn "\n"

def ValidParsedInput (lines : List String) : Prop :=
  lines.length ≥ 2 ∧ IsValidInteger (lines[0]!) ∧ IsValidGameString (lines[1]!) ∧
  let n := StringToInt (lines[0]!)
  let s := lines[1]!
  s.length = n ∧ n ≥ 1

def CountChar (s : String) (c : Char) : Int :=
  s.foldl (fun acc ch => if ch = c then acc + 1 else acc) 0

def DetermineWinner (countA countD : Int) : String :=
  if countA > countD then "Anton"
  else if countD > countA then "Danik"
  else "Friendship"

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input ∧ ValidParsedInput (SplitLines input)
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
  (result = "Anton" ∨ result = "Danik" ∨ result = "Friendship") ∧
  let lines := SplitLines input
  let s := lines[1]!
  let countA := CountChar s 'A'
  let countD := CountChar s 'D'
  result = DetermineWinner countA countD

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>