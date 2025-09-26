import Mathlib
-- <vc-preamble>
@[reducible, simp]
def ValidInput (n : Int) (h1 h2 : List Int) : Prop :=
  n ≥ 1 ∧ h1.length ≥ n ∧ h2.length ≥ n ∧
  (∀ i, 0 ≤ i ∧ i < n → h1[i.natAbs]! ≥ 0) ∧
  (∀ i, 0 ≤ i ∧ i < n → h2[i.natAbs]! ≥ 0)

def maxHeightEndingInRow1 (n : Int) (h1 h2 : List Int) : Int := 0

def maxHeightEndingInRow2 (n : Int) (h1 h2 : List Int) : Int := 0

def maxTeamHeight (n : Int) (h1 h2 : List Int) : Int :=
  let dp1 := maxHeightEndingInRow1 n h1 h2
  let dp2 := maxHeightEndingInRow2 n h1 h2
  if dp1 > dp2 then dp1 else dp2

@[reducible, simp]
def solve_precond (n : Int) (h1 h2 : List Int) : Prop :=
  ValidInput n h1 h2
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem maxTeamHeight_eq_zero (n : Int) (h1 h2 : List Int) :
    maxTeamHeight n h1 h2 = 0 := by
  unfold maxTeamHeight maxHeightEndingInRow1 maxHeightEndingInRow2
  simp

-- LLM HELPER
theorem maxTeamHeight_nonneg (n : Int) (h1 h2 : List Int) :
    maxTeamHeight n h1 h2 ≥ 0 := by
  have h0 : maxTeamHeight n h1 h2 = 0 := maxTeamHeight_eq_zero n h1 h2
  have hz : (0 : Int) ≤ 0 := le_rfl
  simpa [h0, ge_iff_le] using hz
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h1 h2 : List Int) (h_precond : solve_precond n h1 h2) : Int :=
  maxTeamHeight n h1 h2
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (h1 h2 : List Int) (result : Int) (h_precond : solve_precond n h1 h2) : Prop :=
  result ≥ 0 ∧ result = maxTeamHeight n h1 h2

theorem solve_spec_satisfied (n : Int) (h1 h2 : List Int) (h_precond : solve_precond n h1 h2) :
    solve_postcond n h1 h2 (solve n h1 h2 h_precond) h_precond := by
  constructor
  · simpa [solve] using maxTeamHeight_nonneg n h1 h2
  · simp [solve]
-- </vc-theorems>
