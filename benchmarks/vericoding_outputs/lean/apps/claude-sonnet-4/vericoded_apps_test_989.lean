import Mathlib
-- <vc-preamble>
def isDigit (c : Char) : Prop :=
  '0' ≤ c ∧ c ≤ '9'

def hasValidFormat (input : String) : Prop :=
  ∃ firstNewline : Nat, 
    firstNewline < input.length ∧ 
    input.data[firstNewline]! = '\n' ∧
    (input.length = firstNewline + 1 ∨ input.data[input.length - 1]! = '\n')

def ValidInput (input : String) : Prop :=
  input.length ≥ 5 ∧ hasValidFormat input

def IsValidResultString (result : String) : Prop :=
  result.length > 0 ∧ 
  (result = "0" ∨ (result.data[0]! ≠ '0' ∧ ∀ i, 0 ≤ i ∧ i < result.length → isDigit (result.data[i]!)))

def RepresentsMinimumDifference (input : String) (result : String) : Prop :=
  ValidInput input ∧ 
  IsValidResultString result ∧
  result = "0"

def max (a : List Int) : Int :=
  if h : a.length > 0 then
    a.foldl (fun acc x => if x > acc then x else acc) (a.head!)
  else
    0

def min (a : List Int) : Int :=
  if h : a.length > 0 then
    a.foldl (fun acc x => if x < acc then x else acc) (a.head!)
  else
    0

def intToString (n : Int) : String :=
  if n = 0 then "0"
  else if n > 0 then toString n
  else toString n

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Lemma about string "0" being a valid result
lemma isValidResultString_zero : IsValidResultString "0" := by
  constructor
  · -- "0".length > 0
    simp [String.length]
  · -- "0" = "0" ∨ ...
    left
    rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  "0"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  IsValidResultString result ∧ RepresentsMinimumDifference stdin_input result

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  unfold solve_postcond
  constructor
  · -- IsValidResultString "0"
    exact isValidResultString_zero
  · -- RepresentsMinimumDifference stdin_input "0"
    unfold RepresentsMinimumDifference
    constructor
    · -- ValidInput stdin_input
      exact h_precond
    constructor
    · -- IsValidResultString "0"
      exact isValidResultString_zero
    · -- "0" = "0"
      rfl
-- </vc-theorems>
