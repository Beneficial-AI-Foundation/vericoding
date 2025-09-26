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
lemma CountBlocks_ge_one_of_valid (n m : Int) (h : ValidInput n m) :
    1 ≤ CountBlocks n m := by
  rcases h with ⟨hn_ge, _, hm_ge, _⟩
  have hn1 : 1 ≤ n - 1 := by
    have : (1 : Int) + 1 ≤ n := by simpa [one_add_one_eq_two] using hn_ge
    exact (le_sub_iff_add_le).mpr this
  have hm1 : 1 ≤ m - 1 := by
    have : (1 : Int) + 1 ≤ m := by simpa [one_add_one_eq_two] using hm_ge
    exact (le_sub_iff_add_le).mpr this
  have hm_nonneg : 0 ≤ m - 1 := le_trans (show (0 : Int) ≤ 1 from zero_le_one) hm1
  have hmul : 1 * (m - 1) ≤ (n - 1) * (m - 1) :=
    mul_le_mul_of_nonneg_right hn1 hm_nonneg
  have : 1 ≤ (n - 1) * (m - 1) :=
    le_trans (by simpa using hm1) (by simpa using hmul)
  simpa [CountBlocks] using this
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
  unfold solve_postcond
  refine And.intro ?hCorrect ?hGe
  · unfold CorrectOutput
    refine And.intro ?hValid ?hEq
    · simpa [solve_precond] using h_precond
    · simp [solve]
  ·
    have h1 : 1 ≤ CountBlocks n m :=
      CountBlocks_ge_one_of_valid n m (by simpa [solve_precond] using h_precond)
    simpa [solve] using h1
-- </vc-theorems>
