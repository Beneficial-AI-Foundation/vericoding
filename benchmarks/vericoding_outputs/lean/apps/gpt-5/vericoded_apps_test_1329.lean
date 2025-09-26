import Mathlib
-- <vc-preamble>
def ValidInput (N : Int) : Prop :=
  1 ≤ N ∧ N ≤ 100

def countDivisorsWith75Factors (N : Int) (h : ValidInput N) : Int :=
  0

def ValidOutput (result : Int) : Prop :=
  result ≥ 0

@[reducible, simp]
def solve_precond (N : Int) : Prop :=
  ValidInput N
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma countDivisorsWith75Factors_nonneg
    (N : Int) (h : ValidInput N) :
    ValidOutput (countDivisorsWith75Factors N h) := by
  dsimp [countDivisorsWith75Factors, ValidOutput]
  decide
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (h_precond : solve_precond N) : Int :=
  countDivisorsWith75Factors N h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (result : Int) (h_precond : solve_precond N) : Prop :=
  ValidOutput result

theorem solve_spec_satisfied (N : Int) (h_precond : solve_precond N) :
    solve_postcond N (solve N h_precond) h_precond := by
  dsimp [solve_postcond, solve]
  simpa using countDivisorsWith75Factors_nonneg N h_precond
-- </vc-theorems>
