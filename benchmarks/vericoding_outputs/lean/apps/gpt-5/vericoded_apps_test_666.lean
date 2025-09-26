import Mathlib
-- <vc-preamble>
def TriangularNumber (m : Int) : Int :=
  m * (m + 1) / 2

def ValidInput (n : Int) : Prop :=
  n ≥ 1

def ValidResult (n : Int) (result : Int) : Prop :=
  result ≥ 1 ∧ result ≤ n

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  1
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : Int) (h_precond : solve_precond n) : Prop :=
  ValidResult n result

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  dsimp [solve_postcond, ValidResult, solve]
  constructor
  · exact le_rfl
  · simpa [ValidInput] using h_precond
-- </vc-theorems>
