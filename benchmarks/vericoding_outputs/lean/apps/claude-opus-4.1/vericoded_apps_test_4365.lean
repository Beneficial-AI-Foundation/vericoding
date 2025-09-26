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
lemma count_odd_times_even_nonneg (K : Int) (h : 2 ≤ K) : CountOddNumbers K * CountEvenNumbers K ≥ 0 := by
  unfold CountOddNumbers CountEvenNumbers
  have h1 : (K + 1) / 2 ≥ 0 := by
    apply Int.ediv_nonneg
    linarith
    norm_num
  have h2 : K / 2 ≥ 0 := by
    apply Int.ediv_nonneg
    linarith
    norm_num
  apply mul_nonneg h1 h2
-- </vc-helpers>

-- <vc-definitions>
def solve (K : Int) (h_precond : solve_precond K) : Int :=
  CountOddNumbers K * CountEvenNumbers K
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (K : Int) (result : Int) (h_precond : solve_precond K) : Prop :=
  CorrectResult K result ∧ result ≥ 0

theorem solve_spec_satisfied (K : Int) (h_precond : solve_precond K) :
    solve_postcond K (solve K h_precond) h_precond := by
  unfold solve_postcond CorrectResult ExpectedResult solve
  constructor
  · rfl
  · have h_valid : ValidInput K := h_precond
    apply count_odd_times_even_nonneg
    exact h_valid.1
-- </vc-theorems>
