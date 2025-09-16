-- <vc-preamble>
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
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result = "OVERFLOW!!!" ∨ result ≠ "OVERFLOW!!!"

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>
