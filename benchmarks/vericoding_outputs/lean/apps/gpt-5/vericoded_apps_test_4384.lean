import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  1 ≤ n ∧ n ≤ 1998

def ExpectedResult (n : Int) (h : ValidInput n) : String :=
  if n < 1000 then "ABC" else "ABD"

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma expectedResult_def (n : Int) (h : ValidInput n) :
  ExpectedResult n h = (if n < 1000 then "ABC" else "ABD") := rfl

-- LLM HELPER
@[simp] lemma solve_precond_iff (n : Int) : solve_precond n ↔ ValidInput n := Iff.rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : String :=
  if n < 1000 then "ABC" else "ABD"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : String) (h_precond : solve_precond n) : Prop :=
  result = ExpectedResult n h_precond

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  simp [solve_postcond, solve, ExpectedResult]
-- </vc-theorems>
