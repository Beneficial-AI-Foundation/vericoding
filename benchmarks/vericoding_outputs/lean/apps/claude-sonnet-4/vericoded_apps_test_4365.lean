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
-- LLM HELPER: lemmas for integer division properties
lemma int_div_nonneg (a b : Int) (ha : a ≥ 0) (hb : b > 0) : a / b ≥ 0 := by
  exact Int.ediv_nonneg ha (Int.le_of_lt hb)

lemma count_odd_nonneg (K : Int) (hK : K ≥ 2) : CountOddNumbers K ≥ 0 := by
  unfold CountOddNumbers
  exact int_div_nonneg (K + 1) 2 (by linarith) (by norm_num)

lemma count_even_nonneg (K : Int) (hK : K ≥ 2) : CountEvenNumbers K ≥ 0 := by
  unfold CountEvenNumbers  
  exact int_div_nonneg K 2 (by linarith) (by norm_num)
-- </vc-helpers>

-- <vc-definitions>
def solve (K : Int) (h_precond : solve_precond K) : Int :=
  -- LLM HELPER: Direct computation of the expected result
  let odd_count := CountOddNumbers K
  let even_count := CountEvenNumbers K
  odd_count * even_count
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (K : Int) (result : Int) (h_precond : solve_precond K) : Prop :=
  CorrectResult K result ∧ result ≥ 0

theorem solve_spec_satisfied (K : Int) (h_precond : solve_precond K) :
    solve_postcond K (solve K h_precond) h_precond := by
  unfold solve_postcond CorrectResult ExpectedResult
  constructor
  · -- Show solve K h_precond = ExpectedResult K
    rfl
  · -- Show result ≥ 0
    have hK_ge : K ≥ 2 := h_precond.1
    have h_odd_nonneg : CountOddNumbers K ≥ 0 := count_odd_nonneg K hK_ge
    have h_even_nonneg : CountEvenNumbers K ≥ 0 := count_even_nonneg K hK_ge
    exact mul_nonneg h_odd_nonneg h_even_nonneg
-- </vc-theorems>
