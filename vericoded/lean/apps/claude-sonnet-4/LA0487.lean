import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  1 ≤ n ∧ n ≤ 16

def FactTruthValues : List Int :=
  [1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0]

def ValidOutput (result : Int) : Prop :=
  result = 0 ∨ result = 1

def ExpectedOutput (n : Int) (h : ValidInput n) : Int :=
  FactTruthValues[n.natAbs - 1]!

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Lemmas to help with proof
lemma FactTruthValues_valid_indices (i : Nat) (h : i < 16) : 
  FactTruthValues[i]! = 0 ∨ FactTruthValues[i]! = 1 := by
  interval_cases i <;> simp [FactTruthValues]

lemma FactTruthValues_length : FactTruthValues.length = 16 := by
  simp [FactTruthValues]

lemma valid_index_from_ValidInput (n : Int) (h : ValidInput n) :
  n.natAbs - 1 < FactTruthValues.length := by
  have h1 := h.1  -- 1 ≤ n
  have h2 := h.2  -- n ≤ 16
  rw [FactTruthValues_length]
  -- Use interval_cases to handle all possible values of n from 1 to 16
  interval_cases n <;> norm_num
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  -- LLM HELPER: Extract the value from FactTruthValues at the correct index
  FactTruthValues[n.natAbs - 1]!
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : Int) (h_precond : solve_precond n) : Prop :=
  ValidOutput result ∧ result = ExpectedOutput n h_precond

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  -- LLM HELPER: Prove the postcondition is satisfied
  unfold solve_postcond
  constructor
  · -- Prove ValidOutput (solve n h_precond)
    unfold ValidOutput solve
    have h_valid_idx : n.natAbs - 1 < FactTruthValues.length := valid_index_from_ValidInput n h_precond
    have h_in_range : n.natAbs - 1 < 16 := by rw [FactTruthValues_length] at h_valid_idx; exact h_valid_idx
    exact FactTruthValues_valid_indices (n.natAbs - 1) h_in_range
  · -- Prove solve n h_precond = ExpectedOutput n h_precond
    unfold solve ExpectedOutput
    rfl
-- </vc-theorems>
