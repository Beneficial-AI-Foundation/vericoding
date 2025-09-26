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
lemma blocks_ge_one (n m : Int) (h_valid : ValidInput n m) : CountBlocks n m ≥ 1 := by
  unfold CountBlocks
  unfold ValidInput at h_valid
  rcases h_valid with ⟨hn, _, hm, _⟩
  have h_n_minus_1_ge_1 : 1 ≤ n - 1 := by linarith [hn]
  have h_m_minus_1_ge_1 : 1 ≤ m - 1 := by linarith [hm]
  rw [← one_mul (1 : Int)]
  apply mul_le_mul
  · exact h_n_minus_1_ge_1
  · exact h_m_minus_1_ge_1
  · simp -- 0 ≤ 1
  · -- 0 ≤ n - 1
    linarith [hn]


-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (h_precond : solve_precond n m) : Int :=
  (n - 1) * (m - 1)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (blocks : Int) (h_precond : solve_precond n m) : Prop :=
  CorrectOutput n m blocks ∧ blocks ≥ 1

theorem solve_spec_satisfied (n m : Int) (h_precond : solve_precond n m) :
    solve_postcond n m (solve n m h_precond) h_precond := by
  
  simp [solve_postcond, solve, CorrectOutput, CountBlocks, solve_precond]
  constructor
  · exact h_precond
  · exact blocks_ge_one n m h_precond

-- </vc-theorems>
