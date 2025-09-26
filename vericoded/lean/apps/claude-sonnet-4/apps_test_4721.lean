import Mathlib
-- <vc-preamble>
def ValidInput (n m : Int) : Prop :=
  2 ≤ n ∧ n ≤ 100 ∧ 2 ≤ m ∧ m ≤ 100

def CountBlocks (n m : Int) : Int :=
  (n - 1) * (m - 1)

def CorrectOutput (n m blocks : Int) : Prop :=
  ValidInput n m ∧ blocks = CountBlocks n m

@[reducible, simp]
def solve_precond (n m : Int) : Prop :=
  ValidInput n m
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma valid_input_bounds (n m : Int) (h : ValidInput n m) : 
  2 ≤ n ∧ n ≤ 100 ∧ 2 ≤ m ∧ m ≤ 100 := h

-- LLM HELPER
lemma count_blocks_positive (n m : Int) (h : ValidInput n m) : 
  1 ≤ CountBlocks n m := by
  unfold CountBlocks
  have ⟨hn_ge, _, hm_ge, _⟩ := h
  have h1 : 1 ≤ n - 1 := by linarith
  have h2 : 1 ≤ m - 1 := by linarith
  exact one_le_mul_of_one_le_of_one_le h1 h2
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (h_precond : solve_precond n m) : Int :=
  CountBlocks n m
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (blocks : Int) (h_precond : solve_precond n m) : Prop :=
  CorrectOutput n m blocks ∧ blocks ≥ 1

theorem solve_spec_satisfied (n m : Int) (h_precond : solve_precond n m) :
    solve_postcond n m (solve n m h_precond) h_precond := by
  unfold solve_postcond solve CorrectOutput
  constructor
  · constructor
    · exact h_precond
    · rfl
  · exact count_blocks_positive n m h_precond
-- </vc-theorems>
