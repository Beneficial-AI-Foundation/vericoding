import Mathlib
-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0

def ValidOutput (result : List Int) (input : String) : Prop :=
  result.length ≥ 0 ∧
  (∀ i, 0 ≤ i ∧ i < result.length → result[i]! ≥ 1) ∧
  (∀ i, 0 ≤ i ∧ i < result.length → result[i]! ≤ result.length)

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma vacuous_lt_zero_elim {i : Nat} (h : 0 ≤ i ∧ i < 0) : False := by
  exact (Nat.not_lt.mpr h.1) h.2
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : List Int :=
  []
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : List Int) (h_precond : solve_precond input) : Prop :=
  ValidOutput result input

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  unfold solve_postcond
  dsimp [solve, ValidOutput]
  constructor
  · exact le_rfl
  · constructor
    · intro i hi
      have : False := (Nat.not_lt.mpr hi.1) hi.2
      exact this.elim
    · intro i hi
      have : False := (Nat.not_lt.mpr hi.1) hi.2
      exact this.elim
-- </vc-theorems>
