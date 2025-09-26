import Mathlib
-- <vc-preamble>
def ValidInput (n m : Int) : Prop :=
  1 ≤ n ∧ n ≤ 100 ∧ 1 ≤ m ∧ m ≤ n ∧ m ≤ 5

def power (base : Int) (exp : Nat) : Int :=
  if exp = 0 then 1 else base * power base (exp - 1)

def ExpectedTime (n m : Int) : Int :=
  (1900 * m + 100 * (n - m)) * power 2 m.natAbs

@[reducible, simp]
def solve_precond (n m : Int) : Prop :=
  ValidInput n m
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma ExpectedTime_def (n m : Int) :
  ExpectedTime n m = (1900 * m + 100 * (n - m)) * power 2 m.natAbs := rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (h_precond : solve_precond n m) : Int :=
  ExpectedTime n m
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (result : Int) (h_precond : solve_precond n m) : Prop :=
  result = ExpectedTime n m

theorem solve_spec_satisfied (n m : Int) (h_precond : solve_precond n m) :
    solve_postcond n m (solve n m h_precond) h_precond := by
  simpa [solve, solve_postcond]
-- </vc-theorems>
