import Mathlib
-- <vc-preamble>
def ValidInput (A B K : Int) : Prop :=
  A ≥ 0 ∧ B ≥ 0 ∧ K ≥ 0

def ExpectedTakahashiCookies (A B K : Int) (h : ValidInput A B K) : Int :=
  if A ≥ K then A - K else 0

def ExpectedAokiCookies (A B K : Int) (h : ValidInput A B K) : Int :=
  if A ≥ K then B
  else if K - A < B then B - (K - A)
  else 0

def CorrectResult (A B K takahashi aoki : Int) (h : ValidInput A B K) : Prop :=
  takahashi = ExpectedTakahashiCookies A B K h ∧
  aoki = ExpectedAokiCookies A B K h ∧
  takahashi ≥ 0 ∧ aoki ≥ 0

@[reducible, simp]
def solve_precond (A B K : Int) : Prop :=
  ValidInput A B K
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem ExpectedTakahashiCookies_nonneg (A B K : Int) (h : ValidInput A B K) :
    ExpectedTakahashiCookies A B K h ≥ 0 := by
  unfold ExpectedTakahashiCookies
  by_cases hAK : A ≥ K
  · have : 0 ≤ A - K := sub_nonneg.mpr hAK
    simpa [hAK] using this
  · simp [hAK]

-- LLM HELPER
theorem ExpectedAokiCookies_nonneg (A B K : Int) (h : ValidInput A B K) :
    ExpectedAokiCookies A B K h ≥ 0 := by
  unfold ExpectedAokiCookies
  by_cases hAK : A ≥ K
  · simpa [hAK] using h.2.1
  · by_cases hrem : K - A < B
    · have : 0 < B - (K - A) := sub_pos_of_lt hrem
      have : 0 ≤ B - (K - A) := le_of_lt this
      simpa [hAK, hrem] using this
    · simp [hAK, hrem]
-- </vc-helpers>

-- <vc-definitions>
def solve (A B K : Int) (h_precond : solve_precond A B K) : Int × Int :=
  (ExpectedTakahashiCookies A B K h_precond, ExpectedAokiCookies A B K h_precond)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B K : Int) (result : Int × Int) (h_precond : solve_precond A B K) : Prop :=
  CorrectResult A B K result.1 result.2 h_precond

theorem solve_spec_satisfied (A B K : Int) (h_precond : solve_precond A B K) :
    solve_postcond A B K (solve A B K h_precond) h_precond := by
  unfold solve_postcond
  dsimp [solve]
  unfold CorrectResult
  refine And.intro rfl ?h1
  refine And.intro rfl ?h2
  refine And.intro ?h3 ?h4
  · exact ExpectedTakahashiCookies_nonneg A B K h_precond
  · exact ExpectedAokiCookies_nonneg A B K h_precond
-- </vc-theorems>
