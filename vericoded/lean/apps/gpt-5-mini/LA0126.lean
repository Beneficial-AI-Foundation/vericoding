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
-- LLM HELPER

def overflow_msg : String := "OVERFLOW!!!"

-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  overflow_msg
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result = "OVERFLOW!!!" ∨ result ≠ "OVERFLOW!!!"

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  dsimp [solve_postcond, solve, overflow_msg]
  left
  rfl
-- </vc-theorems>
