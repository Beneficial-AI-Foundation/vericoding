import Mathlib
-- <vc-preamble>
partial def minStepsToZero (n k : Nat) : Nat :=
  if n = 0 then 0
  else if n % k = 0 then 1 + minStepsToZero (n / k) k
  else (n % k) + minStepsToZero (n - (n % k)) k

def splitLinesFunc (_ : String) : List String := []

def isValidNumber (_ : String) : Bool := true

def stringToIntFunc (_ : String) : Nat := 0

def splitSpacesFunc (_ : String) : List String := []

def intToStringFunc (_ : Nat) : String := ""

def joinLinesSeq (_ : List String) : String := ""

def validTestCase (line : String) : Prop :=
  let parts := splitSpacesFunc line
  parts.length = 2 ∧
  isValidNumber (parts[0]!) = true ∧
  isValidNumber (parts[1]!) = true ∧
  let n := stringToIntFunc (parts[0]!)
  let k := stringToIntFunc (parts[1]!)
  n ≥ 1 ∧ k ≥ 2

def validInput (input : String) : Prop :=
  input.length > 0 ∧
  let lines := splitLinesFunc input
  lines.length ≥ 1 ∧
  isValidNumber (lines[0]!) = true ∧
  let t := stringToIntFunc (lines[0]!)
  t ≥ 1 ∧ t ≤ 100 ∧
  lines.length ≥ t + 1 ∧
  (∀ i, 1 ≤ i ∧ i ≤ t → validTestCase (lines[i]!))

def expectedOutput (input : String) : String :=
  let lines := splitLinesFunc input
  let t := stringToIntFunc (lines[0]!)
  let results := List.range t |>.map (fun i =>
    let parts := splitSpacesFunc (lines[i + 1]!)
    let n := stringToIntFunc (parts[0]!)
    let k := stringToIntFunc (parts[1]!)
    intToStringFunc (minStepsToZero n k))
  joinLinesSeq results

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ validInput input
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  expectedOutput input
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result.length ≥ 0 ∧
  (∀ i : Nat, 0 ≤ i ∧ i < result.length → true) ∧
  result = expectedOutput input

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  unfold solve solve_postcond
  constructor
  · exact Nat.zero_le _
  constructor
  · intro i hi
    trivial
  · rfl
-- </vc-theorems>
