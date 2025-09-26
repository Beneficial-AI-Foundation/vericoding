import Mathlib
-- <vc-preamble>
def ValidInput (n k : Int) : Prop :=
  n ≥ 0 ∧ k ≥ 1

def MinValue (n k : Int) (h : ValidInput n k) : Int :=
  let remainder := n % k
  let complement := k - remainder
  if remainder ≤ complement then remainder else complement

def IsCorrectResult (n k result : Int) (h : ValidInput n k) : Prop :=
  result = MinValue n k h ∧
  result ≥ 0 ∧
  result < k

@[reducible, simp]
def solve_precond (n k : Int) : Prop :=
  ValidInput n k
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Properties of modular arithmetic and MinValue
lemma mod_nonneg_of_pos (n : Int) (k : Int) (hk : k > 0) : 0 ≤ n % k := by
  exact Int.emod_nonneg n (ne_of_gt hk)

lemma mod_lt_of_pos (n : Int) (k : Int) (hk : k > 0) : n % k < k := by
  exact Int.emod_lt_of_pos n hk

lemma MinValue_nonneg (n k : Int) (h : ValidInput n k) : 0 ≤ MinValue n k h := by
  unfold MinValue
  simp only [ValidInput] at h
  by_cases hcond : (n % k) ≤ (k - (n % k))
  · simp [hcond]
    exact mod_nonneg_of_pos n k h.2
  · simp [hcond]
    have h_mod_nonneg : 0 ≤ n % k := mod_nonneg_of_pos n k h.2
    have h_mod_lt : n % k < k := mod_lt_of_pos n k h.2
    omega

lemma MinValue_lt (n k : Int) (h : ValidInput n k) : MinValue n k h < k := by
  unfold MinValue
  simp only [ValidInput] at h
  by_cases hcond : (n % k) ≤ (k - (n % k))
  · simp [hcond]
    exact mod_lt_of_pos n k h.2
  · simp [hcond]
    have h_mod_nonneg : 0 ≤ n % k := mod_nonneg_of_pos n k h.2
    have h_mod_lt : n % k < k := mod_lt_of_pos n k h.2
    omega
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (h_precond : solve_precond n k) : Int :=
  MinValue n k h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (result : Int) (h_precond : solve_precond n k) : Prop :=
  IsCorrectResult n k result h_precond

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  unfold solve_postcond IsCorrectResult
  constructor
  · rfl
  constructor
  · exact MinValue_nonneg n k h_precond
  · exact MinValue_lt n k h_precond
-- </vc-theorems>
