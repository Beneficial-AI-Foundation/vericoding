import Mathlib
-- <vc-preamble>
def ValidInput (A1 A2 A3 : Int) : Prop :=
  1 ≤ A1 ∧ A1 ≤ 100 ∧ 1 ≤ A2 ∧ A2 ≤ 100 ∧ 1 ≤ A3 ∧ A3 ≤ 100

def MaxOfThree (A1 A2 A3 : Int) : Int :=
  if A1 ≥ A2 ∧ A1 ≥ A3 then A1 else if A2 ≥ A3 then A2 else A3

def MinOfThree (A1 A2 A3 : Int) : Int :=
  if A1 ≤ A2 ∧ A1 ≤ A3 then A1 else if A2 ≤ A3 then A2 else A3

def MinimumCost (A1 A2 A3 : Int) : Int :=
  MaxOfThree A1 A2 A3 - MinOfThree A1 A2 A3

@[reducible, simp]
def solve_precond (A1 A2 A3 : Int) : Prop :=
  ValidInput A1 A2 A3
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem MinimumCost_eq (A1 A2 A3 : Int) : MinimumCost A1 A2 A3 = MaxOfThree A1 A2 A3 - MinOfThree A1 A2 A3 := rfl
-- LLM HELPER
@[simp] theorem MaxOfThree_eq (A1 A2 A3 : Int) : MaxOfThree A1 A2 A3 = if A1 ≥ A2 ∧ A1 ≥ A3 then A1 else if A2 ≥ A3 then A2 else A3 := rfl
-- LLM HELPER
@[simp] theorem MinOfThree_eq (A1 A2 A3 : Int) : MinOfThree A1 A2 A3 = if A1 ≤ A2 ∧ A1 ≤ A3 then A1 else if A2 ≤ A3 then A2 else A3 := rfl
-- LLM HELPER
lemma MinimumCost_nonneg (A1 A2 A3 : Int) : MinimumCost A1 A2 A3 ≥ 0 := by
  unfold MinimumCost MaxOfThree MinOfThree
  grind
-- </vc-helpers>

-- <vc-definitions>
def solve (A1 A2 A3 : Int) (h_precond : solve_precond A1 A2 A3) : Int :=
  MinimumCost A1 A2 A3
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A1 A2 A3 : Int) (result: Int) (h_precond : solve_precond A1 A2 A3) : Prop :=
  result ≥ 0 ∧ result = MinimumCost A1 A2 A3

theorem solve_spec_satisfied (A1 A2 A3 : Int) (h_precond : solve_precond A1 A2 A3) :
    solve_postcond A1 A2 A3 (solve A1 A2 A3 h_precond) h_precond := by
  have lem : MinimumCost A1 A2 A3 ≥ 0 := MinimumCost_nonneg A1 A2 A3
  simp [solve_postcond]
  constructor
  · exact lem
  · unfold solve; rfl
-- </vc-theorems>
