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
theorem eq_or_ne_overflow (s : String) : s = "OVERFLOW!!!" ∨ s ≠ "OVERFLOW!!!" := by
  by_cases h : s = "OVERFLOW!!!"
  · exact Or.inl h
  · exact Or.inr h
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  input
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result = "OVERFLOW!!!" ∨ result ≠ "OVERFLOW!!!"

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  simpa [solve_postcond] using eq_or_ne_overflow (solve input h_precond)
-- </vc-theorems>
