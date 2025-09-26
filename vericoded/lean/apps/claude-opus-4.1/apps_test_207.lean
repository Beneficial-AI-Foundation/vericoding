import Mathlib
-- <vc-preamble>
def ValidInput (a : List Int) : Prop :=
  a.length ≥ 1

def CanBeDivided (a : List Int) : Prop :=
  a.length % 2 = 1 ∧ a[0]! % 2 = 1 ∧ a[a.length - 1]! % 2 = 1

@[reducible, simp]
def solve_precond (a : List Int) : Prop :=
  ValidInput a
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
instance canBeDivided_decidable (a : List Int) : Decidable (CanBeDivided a) := by
  unfold CanBeDivided
  infer_instance
-- </vc-helpers>

-- <vc-definitions>
def solve (a : List Int) (h_precond : solve_precond a) : String :=
  if canBeDivided : CanBeDivided a then "Yes" else "No"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a : List Int) (result : String) (h_precond : solve_precond a) : Prop :=
  (CanBeDivided a → result = "Yes") ∧ (¬CanBeDivided a → result = "No")

theorem solve_spec_satisfied (a : List Int) (h_precond : solve_precond a) :
    solve_postcond a (solve a h_precond) h_precond := by
  unfold solve_postcond solve
  split_ifs with h
  · constructor
    · intro _; rfl
    · intro neg; contradiction
  · constructor
    · intro pos; contradiction
    · intro _; rfl
-- </vc-theorems>
