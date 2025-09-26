import Mathlib
-- <vc-preamble>
def sum_abs (arr : List Int) (i : Nat) : Int :=
  if h : i < arr.length then
    let elem := arr[i]
    (if elem ≥ 0 then elem else -elem) + sum_abs arr (i + 1)
  else 0
termination_by arr.length - i

def ValidInput (n : Int) (arr : List Int) : Prop :=
  0 ≤ n ∧ n = arr.length

@[reducible, simp]
def solve_precond (n : Int) (arr : List Int) : Prop :=
  ValidInput n arr
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma solve_precond_def (n : Int) (arr : List Int) :
  solve_precond n arr = ValidInput n arr := rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (arr : List Int) (h_precond : solve_precond n arr) : Int :=
  sum_abs arr 0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (arr : List Int) (result : Int) (h_precond : solve_precond n arr) : Prop :=
  result = sum_abs arr 0

theorem solve_spec_satisfied (n : Int) (arr : List Int) (h_precond : solve_precond n arr) :
    solve_postcond n arr (solve n arr h_precond) h_precond := by
  simp [solve, solve_postcond]
-- </vc-theorems>
