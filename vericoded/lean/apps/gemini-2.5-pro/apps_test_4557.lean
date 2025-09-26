import Mathlib
-- <vc-preamble>
def ValidInput (a b x : Int) : Prop :=
  1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100 ∧ 1 ≤ x ∧ x ≤ 200

def CanHaveExactlyCats (a b x : Int) : Prop :=
  a ≤ x ∧ x ≤ a + b

@[reducible, simp]
def solve_precond (a b x : Int) : Prop :=
  ValidInput a b x
-- </vc-preamble>

-- <vc-helpers>

-- LLM HELPER
instance (a b x : Int) : Decidable (CanHaveExactlyCats a b x) := by
  unfold CanHaveExactlyCats
  infer_instance

-- </vc-helpers>

-- <vc-definitions>
def solve (a b x : Int) (h_precond : solve_precond a b x) : String :=
  if CanHaveExactlyCats a b x then "YES" else "NO"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b x : Int) (result : String) (h_precond : solve_precond a b x) : Prop :=
  (result = "YES") ↔ CanHaveExactlyCats a b x

theorem solve_spec_satisfied (a b x : Int) (h_precond : solve_precond a b x) :
    solve_postcond a b x (solve a b x h_precond) h_precond := by
  simp [solve, solve_postcond]
-- </vc-theorems>
