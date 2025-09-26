import Mathlib
-- <vc-preamble>
def ValidInput (lines : List String) : Prop :=
  lines.length > 0

def MAX_VALUE : Int := 4294967295

def IsOverflow (x : Int) : Prop :=
  x > MAX_VALUE

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput [input]
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Parse input string as integer if possible
def parseIntSafe (s : String) : Option Int :=
  s.toInt?

-- LLM HELPER: Check if parsed integer would overflow
def checkOverflow (n : Int) : Bool :=
  n > MAX_VALUE
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  match parseIntSafe input with
  | some n => if checkOverflow n then "OVERFLOW!!!" else toString n
  | none => "INVALID"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result = "OVERFLOW!!!" ∨ result ≠ "OVERFLOW!!!"

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  -- The postcondition is a tautology: P ∨ ¬P
  unfold solve_postcond
  by_cases h : solve input h_precond = "OVERFLOW!!!"
  · left; exact h
  · right; exact h
-- </vc-theorems>
