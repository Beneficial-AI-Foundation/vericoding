import Mathlib
-- <vc-preamble>
def ValidInput (n v : Int) : Prop :=
  2 ≤ n ∧ n ≤ 100 ∧ 1 ≤ v ∧ v ≤ 100

def MinCost (n v : Int) (h : ValidInput n v) : Int :=
  let req := n - 1
  if req ≤ v then
    req
  else
    let remaining := req - v
    v + remaining * (remaining + 3) / 2

@[reducible, simp]
def solve_precond (n v : Int) : Prop :=
  ValidInput n v
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma solve_precond_iff (n v : Int) : solve_precond n v = ValidInput n v := rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (n v : Int) (h_precond : solve_precond n v) : Int :=
  MinCost n v h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n v : Int) (result : Int) (h_precond : solve_precond n v) : Prop :=
  result = MinCost n v h_precond

theorem solve_spec_satisfied (n v : Int) (h_precond : solve_precond n v) :
    solve_postcond n v (solve n v h_precond) h_precond := by
  simp [solve_postcond, solve]
-- </vc-theorems>
