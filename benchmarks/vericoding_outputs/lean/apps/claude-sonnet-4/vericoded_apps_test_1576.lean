import Mathlib
-- <vc-preamble>
def ValidInput (t : String) : Prop :=
  t.length ≥ 1

@[reducible, simp]
def solve_precond (t : String) : Prop :=
  ValidInput t
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: No additional helpers needed for this simple case
-- </vc-helpers>

-- <vc-definitions>
def solve (t : String) (h_precond : solve_precond t) : String :=
  t
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (t : String) (result : String) (h_precond : solve_precond t) : Prop :=
  result.length = t.length

theorem solve_spec_satisfied (t : String) (h_precond : solve_precond t) :
    solve_postcond t (solve t h_precond) h_precond := by
  unfold solve_postcond solve
  simp
-- </vc-theorems>
