import Mathlib
-- <vc-preamble>
def ValidInput (A B T : Int) : Prop :=
  1 ≤ A ∧ A ≤ 20 ∧ 1 ≤ B ∧ B ≤ 20 ∧ 1 ≤ T ∧ T ≤ 20

def ProductionCount (A T : Int) : Int :=
  if A > 0 then T / A else 0

def TotalBiscuits (A B T : Int) : Int :=
  if A > 0 then B * ProductionCount A T else 0

@[reducible, simp]
def solve_precond (A B T : Int) : Prop :=
  ValidInput A B T
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- From `ValidInput`, we can prove that `A` is positive. -/
lemma A_pos_of_valid_input {A B T : Int} (h : ValidInput A B T) : 0 < A := by
  linarith [h.1]
-- </vc-helpers>

-- <vc-definitions>
def solve (A B T : Int) (h_precond : solve_precond A B T) : Int :=
  B * (T / A)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B T : Int) (result : Int) (h_precond : solve_precond A B T) : Prop :=
  result = TotalBiscuits A B T

theorem solve_spec_satisfied (A B T : Int) (h_precond : solve_precond A B T) :
    solve_postcond A B T (solve A B T h_precond) h_precond := by
    -- Unfold the core components of the proposition to be proved.
  simp [solve, solve_postcond]
  -- The goal is now `B * (T / A) = TotalBiscuits A B T`.
  -- The definitions of `TotalBiscuits` and `ProductionCount` use `if 0 < A ...`.
  -- We can prove `0 < A` using our helper lemma and the precondition `h_precond`.
  have hA_pos : 0 < A := A_pos_of_valid_input h_precond
  -- `simp` can use `hA_pos` to simplify the `if` statements inside the definitions.
  simp [TotalBiscuits, ProductionCount, hA_pos]
-- </vc-theorems>
