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
-- LLM HELPER: Decidability instance for CanHaveExactlyCats
instance (a b x : Int) : Decidable (CanHaveExactlyCats a b x) :=
  show Decidable (a ≤ x ∧ x ≤ a + b) from inferInstance
-- </vc-helpers>

-- <vc-definitions>
def solve (a b x : Int) (h_precond : solve_precond a b x) : String :=
  if a ≤ x ∧ x ≤ a + b then "YES" else "NO"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b x : Int) (result : String) (h_precond : solve_precond a b x) : Prop :=
  (result = "YES") ↔ CanHaveExactlyCats a b x

theorem solve_spec_satisfied (a b x : Int) (h_precond : solve_precond a b x) :
    solve_postcond a b x (solve a b x h_precond) h_precond := by
  unfold solve_postcond solve CanHaveExactlyCats
  split_ifs with h
  · constructor
    · intro
      exact h
    · intro
      rfl
  · constructor
    · intro h_eq
      exfalso
      simp at h_eq
    · intro h_can
      exfalso
      exact h h_can
-- </vc-theorems>
