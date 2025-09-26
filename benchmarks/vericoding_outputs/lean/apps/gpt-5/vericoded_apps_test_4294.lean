import Mathlib
-- <vc-preamble>
@[reducible, simp]
def solve_precond (x a : Int) : Prop :=
  0 ≤ x ∧ x ≤ 9 ∧ 0 ≤ a ∧ a ≤ 9
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma ifInt_self (x a : Int) :
    (if x < a then (0:Int) else 10) = (if x < a then 0 else 10) := rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (x a : Int) (h_precond : solve_precond x a) : Int :=
  if x < a then 0 else 10
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x a : Int) (result : Int) (h_precond : solve_precond x a) : Prop :=
  result = (if x < a then 0 else 10)

theorem solve_spec_satisfied (x a : Int) (h_precond : solve_precond x a) :
    solve_postcond x a (solve x a h_precond) h_precond := by
  unfold solve_postcond
  simp [solve]
-- </vc-theorems>
