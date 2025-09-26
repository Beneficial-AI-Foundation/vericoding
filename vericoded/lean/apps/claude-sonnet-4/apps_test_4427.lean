import Mathlib
-- <vc-preamble>
def parseInputPure (input : String) : List Int :=
  []  -- Placeholder implementation

def intToString (n : Int) : String :=
  toString n

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧
  let tokens := parseInputPure input
  tokens.length = 3 ∧
  2 ≤ tokens[0]! ∧ tokens[0]! ≤ 5 ∧
  1 ≤ tokens[1]! ∧ tokens[1]! ≤ 100 ∧
  tokens[1]! < tokens[2]! ∧ tokens[2]! ≤ 200

def calculateRecurrence (r D x0 : Int) : Nat → Int
  | 0 => x0
  | n + 1 => r * calculateRecurrence r D x0 n - D

def generateOutputUpToIteration (r D x0 : Int) : Nat → String
  | 0 => ""
  | iterations + 1 =>
      let currentValue := calculateRecurrence r D x0 iterations
      let previousOutput := generateOutputUpToIteration r D x0 iterations
      previousOutput ++ intToString currentValue ++ "\n"

def generateExpectedOutput (r D x0 : Int) : String :=
  generateOutputUpToIteration r D x0 10

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Parse a string into a list of integers
def parseStringToInts (s : String) : List Int :=
  s.splitOn " " |>.filterMap (fun token => token.trim.toInt?)

-- LLM HELPER: Safe list indexing with default
def getOrDefault (l : List Int) (i : Nat) (default : Int) : Int :=
  l.getD i default
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  let tokens := parseInputPure input
  let r := tokens[0]!
  let D := tokens[1]!
  let x0 := tokens[2]!
  generateExpectedOutput r D x0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  let tokens := parseInputPure input
  result = generateExpectedOutput tokens[0]! tokens[1]! tokens[2]!

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  unfold solve_postcond solve
  rfl
-- </vc-theorems>
