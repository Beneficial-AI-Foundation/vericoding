-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0 ∧
  ∃ spaceIndex, 0 ≤ spaceIndex ∧ spaceIndex < input.length ∧ input.data[spaceIndex]! = ' ' ∧
  ∀ i, 0 ≤ i ∧ i < input.length → (input.data[i]! = ' ' ∨ ('0' ≤ input.data[i]! ∧ input.data[i]! ≤ '9'))

def FindSpace (s : String) (start : Nat) : Int :=
  if h : start < s.length then
    if s.data[start]! = ' ' then start
    else FindSpace s (start + 1)
  else -1
  termination_by s.length - start

def StringToInt (s : String) : Int :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def isAllDigits (s : String) : Bool :=
  s.all (fun c => '0' ≤ c ∧ c ≤ '9')

def ParseTwoInts (s : String) : Int × Int :=
  let spaceIndex := FindSpace s 0
  if spaceIndex = -1 ∨ spaceIndex = 0 ∨ spaceIndex = s.length - 1 then (1, 1)
  else
    let firstPart := s.take spaceIndex.natAbs
    let secondPart := s.drop (spaceIndex.natAbs + 1)
    if firstPart.length = 0 ∨ secondPart.length = 0 then (1, 1)
    else if ¬(isAllDigits firstPart) then (1, 1)
    else if ¬(isAllDigits secondPart) then (1, 1)
    else
      let first := StringToInt firstPart
      let second := StringToInt secondPart
      if first ≤ 0 ∨ second ≤ 0 then (1, 1)
      else (first, second)

def LCM (a b : Int) : Int :=
  if a > 0 ∧ b > 0 then (a * b) / Int.gcd a b else 1

def ValidOutput (output : String) : Prop :=
  output.length > 0 ∧
  ∀ i, 0 ≤ i ∧ i < output.length → ('0' ≤ output.data[i]! ∧ output.data[i]! ≤ '9')

def IntToString (n : Int) : String :=
  toString n.natAbs

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
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
  let nums := ParseTwoInts input
  let a := nums.1
  let b := nums.2
  result = IntToString (LCM a b) ∧
  ValidOutput result

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>