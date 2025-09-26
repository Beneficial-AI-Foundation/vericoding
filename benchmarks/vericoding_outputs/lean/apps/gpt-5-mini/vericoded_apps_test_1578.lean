import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  n ≥ 1

def MaxSum (n : Int) : Int :=
  n * (n - 1) / 2

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- LLM HELPER
-- A trivial helper stating the definition of MaxSum (keeps a named lemma available if needed)
theorem MaxSum_def (n : Int) : MaxSum n = n * (n - 1) / 2 := rfl

-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  MaxSum n
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : Int) (h_precond : solve_precond n) : Prop :=
  result = MaxSum n

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  rfl
-- </vc-theorems>
