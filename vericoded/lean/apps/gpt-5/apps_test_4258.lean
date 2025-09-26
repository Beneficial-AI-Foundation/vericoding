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
@[simp] lemma ProductionCount_nonpos_A (A T : Int) (hA : ¬ A > 0) :
  ProductionCount A T = 0 := by
  simp [ProductionCount, hA]

-- LLM HELPER
@[simp] lemma TotalBiscuits_nonpos_A (A B T : Int) (hA : ¬ A > 0) :
  TotalBiscuits A B T = 0 := by
  simp [TotalBiscuits, hA]

-- LLM HELPER
@[simp] lemma TotalBiscuits_pos_A (A B T : Int) (hA : A > 0) :
  TotalBiscuits A B T = B * (T / A) := by
  simp [TotalBiscuits, ProductionCount, hA]
-- </vc-helpers>

-- <vc-definitions>
def solve (A B T : Int) (h_precond : solve_precond A B T) : Int :=
  TotalBiscuits A B T
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B T : Int) (result : Int) (h_precond : solve_precond A B T) : Prop :=
  result = TotalBiscuits A B T

theorem solve_spec_satisfied (A B T : Int) (h_precond : solve_precond A B T) :
    solve_postcond A B T (solve A B T h_precond) h_precond := by
  rfl
-- </vc-theorems>
