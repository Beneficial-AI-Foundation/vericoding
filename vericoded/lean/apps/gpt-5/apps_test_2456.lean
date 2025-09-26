import Mathlib
-- <vc-preamble>
@[reducible, simp]
def ValidInput (n r : Int) : Prop :=
  n ≥ 1 ∧ r ≥ 1

def ExpectedResult (n r : Int) (h : ValidInput n r) : Int :=
  let k := if r < n - 1 then r else n - 1
  k * (k + 1) / 2 + (if r ≥ n then 1 else 0)

@[reducible, simp]
def solve_precond (n r : Int) : Prop :=
  ValidInput n r
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem solve_precond_eq {n r : Int} :
  solve_precond n r = ValidInput n r := rfl

-- LLM HELPER
@[simp] theorem solve_precond_iff {n r : Int} :
  solve_precond n r ↔ ValidInput n r := Iff.rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (n r : Int) (h_precond : solve_precond n r) : Int :=
  ExpectedResult n r h_precond
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>
