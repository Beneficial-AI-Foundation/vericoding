import Mathlib
-- <vc-preamble>
def ValidInput (K : Int) : Prop :=
  2 ≤ K ∧ K ≤ 100

def CountOddNumbers (K : Int) : Int :=
  (K + 1) / 2

def CountEvenNumbers (K : Int) : Int :=
  K / 2

def ExpectedResult (K : Int) : Int :=
  CountOddNumbers K * CountEvenNumbers K

def CorrectResult (K : Int) (result : Int) : Prop :=
  result = ExpectedResult K

@[reducible, simp]
def solve_precond (K : Int) : Prop :=
  ValidInput K
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
private theorem count_odd_nonneg_of_valid_input (K : Int) (h_valid : ValidInput K) : 0 ≤ CountOddNumbers K := by
  rcases h_valid with ⟨h_lower, _⟩
  dsimp [CountOddNumbers]
  apply Int.ediv_nonneg
  · linarith [h_lower]
  · norm_num

-- LLM HELPER
private theorem count_even_nonneg_of_valid_input (K : Int) (h_valid : ValidInput K) : 0 ≤ CountEvenNumbers K := by
  rcases h_valid with ⟨h_lower, _⟩
  dsimp [CountEvenNumbers]
  apply Int.ediv_nonneg
  · linarith [h_lower]
  · norm_num
-- </vc-helpers>

-- <vc-definitions>
def solve (K : Int) (h_precond : solve_precond K) : Int :=
  ExpectedResult K
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (K : Int) (result : Int) (h_precond : solve_precond K) : Prop :=
  CorrectResult K result ∧ result ≥ 0

theorem solve_spec_satisfied (K : Int) (h_precond : solve_precond K) :
    solve_postcond K (solve K h_precond) h_precond := by
  {
  constructor
  · simp [solve, CorrectResult, ExpectedResult]
  · simp [solve, ExpectedResult]
    apply mul_nonneg
    · exact count_odd_nonneg_of_valid_input K h_precond
    · exact count_even_nonneg_of_valid_input K h_precond
}
-- </vc-theorems>
