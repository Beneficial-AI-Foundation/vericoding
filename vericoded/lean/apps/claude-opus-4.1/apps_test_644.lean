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
-- No additional helpers needed
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  match input.toInt? with
  | none => "OVERFLOW!!!"
  | some n => if n > MAX_VALUE then "OVERFLOW!!!" else input
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result = "OVERFLOW!!!" ∨ result ≠ "OVERFLOW!!!"

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  simp [solve_postcond, solve]
  split
  · -- Case: input.toInt? = none
    left
    rfl
  · -- Case: input.toInt? = some val  
    split
    · -- Case: val > MAX_VALUE
      left
      rfl
    · -- Case: val ≤ MAX_VALUE
      -- We return input, which may or may not be "OVERFLOW!!!"
      by_cases h : input = "OVERFLOW!!!"
      · left
        exact h
      · right
        exact h
-- </vc-theorems>
