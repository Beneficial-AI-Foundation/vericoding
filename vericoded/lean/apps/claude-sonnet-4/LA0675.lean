import Mathlib
-- <vc-preamble>
def ValidInput (A B : Int) : Prop :=
  1 ≤ A ∧ A ≤ 100 ∧ 1 ≤ B ∧ B ≤ 100

def DistributionPossible (A B : Int) : Prop :=
  A % 3 = 0 ∨ B % 3 = 0 ∨ (A + B) % 3 = 0

@[reducible, simp]
def solve_precond (A B : Int) : Prop :=
  ValidInput A B
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Decidability instance for DistributionPossible
instance (A B : Int) : Decidable (DistributionPossible A B) := by
  unfold DistributionPossible
  infer_instance
-- </vc-helpers>

-- <vc-definitions>
def solve (A B : Int) (h_precond : solve_precond A B) : String :=
  if DistributionPossible A B then "Possible" else "Impossible"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B : Int) (result : String) (h_precond : solve_precond A B) : Prop :=
  (result = "Possible" ↔ DistributionPossible A B) ∧ (result = "Possible" ∨ result = "Impossible")

theorem solve_spec_satisfied (A B : Int) (h_precond : solve_precond A B) :
    solve_postcond A B (solve A B h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · constructor
    · intro h
      split at h
      · assumption
      · contradiction
    · intro h
      split
      · rfl
      · contradiction
  · split
    · left; rfl
    · right; rfl
-- </vc-theorems>
