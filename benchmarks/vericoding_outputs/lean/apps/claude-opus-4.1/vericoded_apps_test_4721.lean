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
lemma min_blocks_positive (n m : Int) (h : ValidInput n m) : (n - 1) * (m - 1) ≥ 1 := by
  unfold ValidInput at h
  have hn : n ≥ 2 := h.1
  have hm : m ≥ 2 := h.2.2.1
  have h1 : n - 1 ≥ 1 := by linarith
  have h2 : m - 1 ≥ 1 := by linarith
  have : (n - 1) * (m - 1) ≥ 1 * 1 := by
    apply mul_le_mul
    · exact h1
    · exact h2
    · linarith
    · linarith
  linarith
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
  unfold solve_postcond solve
  constructor
  · -- Prove CorrectOutput n m (CountBlocks n m)
    unfold CorrectOutput
    exact ⟨h_precond, rfl⟩
  · -- Prove CountBlocks n m ≥ 1
    unfold CountBlocks
    exact min_blocks_positive n m h_precond
-- </vc-theorems>
