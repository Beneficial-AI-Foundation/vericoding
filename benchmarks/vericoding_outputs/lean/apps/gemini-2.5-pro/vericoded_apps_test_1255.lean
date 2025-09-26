import Mathlib
-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0

def SplitLinesHelper (s : String) (start i : Nat) (acc : List String) : List String :=
  if h : i >= s.length then
    if start < s.length then acc ++ [s.drop start] else acc
  else if s.data[i]! = '\n' then
    let newAcc := if start < i then acc ++ [s.drop start |>.take (i - start)] else acc
    SplitLinesHelper s (i + 1) (i + 1) newAcc
  else
    SplitLinesHelper s start (i + 1) acc
  termination_by s.length - i

def SplitLinesFunction (s : String) : List String :=
  SplitLinesHelper s 0 0 []

def CountOccurrencesHelper (lines : List String) (target : String) (index count : Nat) : Nat :=
  if index >= lines.length then count
  else
    let newCount := if lines[index]! = target then count + 1 else count
    CountOccurrencesHelper lines target (index + 1) newCount
  termination_by lines.length - index

def CountOccurrences (lines : List String) (target : String) : Nat :=
  CountOccurrencesHelper lines target 0 0

partial def SkipIdentical (lines : List String) (index : Nat) : Nat :=
  if index + 1 >= lines.length then lines.length
  else if lines[index + 1]! = lines[index]! then SkipIdentical lines (index + 1)
  else index + 1

partial def MaxFrequencyHelper (lines : List String) (index currentMax : Nat) : Nat :=
  if index >= lines.length then currentMax
  else
    let count := CountOccurrences lines (lines[index]!)
    let newMax := if count > currentMax then count else currentMax
    let nextIndex := SkipIdentical lines index
    MaxFrequencyHelper lines nextIndex newMax

def MaxFrequencyInAllLines (lines : List String) : Nat :=
  if lines.length > 0 then MaxFrequencyHelper lines 0 0 else 0

def GetMaxSimultaneousArrivals (input : String) : Int :=
  let lines := SplitLinesFunction input
  if lines.length = 0 then 0
  else Int.ofNat (MaxFrequencyInAllLines lines)

def IntToStringHelper (n : Nat) (acc : String) : String :=
  let digit := n % 10
  let digitChar := Char.ofNat (48 + digit)
  if n / 10 = 0 then digitChar.toString ++ acc
  else IntToStringHelper (n / 10) (digitChar.toString ++ acc)
  termination_by n

def IntToStringFunction (n : Int) : String :=
  if n ≤ 0 then "0"
  else IntToStringHelper n.natAbs ""

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  IntToStringFunction (GetMaxSimultaneousArrivals input) ++ "\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result.length > 0 ∧ result = IntToStringFunction (GetMaxSimultaneousArrivals input) ++ "\n"

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  simp [solve, solve_postcond]
  right
  decide
-- </vc-theorems>
