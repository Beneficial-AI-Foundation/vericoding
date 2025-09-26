import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  n ≥ 3

def MinJumps (n : Int) : Int :=
  (n - 2) * (n - 2)

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma solve_precond_iff (n : Int) : solve_precond n ↔ n ≥ 3 := Iff.rfl

-- LLM HELPER
@[simp] lemma MinJumps_def (n : Int) : MinJumps n = (n - 2) * (n - 2) := rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  MinJumps n
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result: Int) (h_precond : solve_precond n) : Prop :=
  result = MinJumps n

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  simp [solve_postcond, solve]
-- </vc-theorems>
