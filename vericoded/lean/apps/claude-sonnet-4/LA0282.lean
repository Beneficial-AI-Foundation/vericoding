import Mathlib
-- <vc-preamble>
def ValidInput (n m a b : Int) : Prop :=
  n ≥ 1 ∧ n ≤ 1000 ∧
  m ≥ 1 ∧ m ≤ 1000 ∧
  a ≥ 1 ∧ a ≤ 1000 ∧
  b ≥ 1 ∧ b ≤ 1000

def OptimalCost (n m a b : Int) (h : ValidInput n m a b) : Int :=
  min (n * a) (min (((n + m - 1) / m) * b) ((n / m) * b + (n % m) * a))

@[reducible, simp]
def solve_precond (n m a b : Int) : Prop :=
  ValidInput n m a b
-- </vc-preamble>

-- <vc-helpers>
-- Helper lemmas for the optimal cost calculation
lemma min_nonneg_of_nonneg {x y z : Int} (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : min x (min y z) ≥ 0 := by
  simp [min_def]
  split_ifs <;> assumption

lemma div_ceil_nonneg (n m : Int) (hn : n ≥ 1) (hm : m ≥ 1) : (n + m - 1) / m ≥ 0 := by
  have h1 : n + m - 1 ≥ m := by linarith
  have h2 : m > 0 := by linarith
  exact Int.ediv_nonneg (by linarith) (by linarith)

lemma div_mod_nonneg (n m : Int) (hn : n ≥ 1) (hm : m ≥ 1) : n / m ≥ 0 ∧ n % m ≥ 0 := by
  constructor
  · exact Int.ediv_nonneg (by linarith) (by linarith)
  · exact Int.emod_nonneg n (by linarith : m ≠ 0)
-- </vc-helpers>

-- <vc-definitions>
def solve (n m a b : Int) (h_precond : solve_precond n m a b) : Int :=
  min (n * a) (min (((n + m - 1) / m) * b) ((n / m) * b + (n % m) * a))
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m a b : Int) (result : Int) (h_precond : solve_precond n m a b) : Prop :=
  result ≥ 0 ∧ result = OptimalCost n m a b h_precond

theorem solve_spec_satisfied (n m a b : Int) (h_precond : solve_precond n m a b) :
    solve_postcond n m a b (solve n m a b h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · -- Prove result ≥ 0
    have h_valid := h_precond
    unfold ValidInput at h_valid
    obtain ⟨hn_pos, hn_le, hm_pos, hm_le, ha_pos, ha_le, hb_pos, hb_le⟩ := h_valid
    -- Show each component is non-negative
    have h1 : n * a ≥ 0 := Int.mul_nonneg (by linarith) (by linarith)
    have h2 : ((n + m - 1) / m) * b ≥ 0 := Int.mul_nonneg (div_ceil_nonneg n m hn_pos hm_pos) (by linarith)
    have h3_parts := div_mod_nonneg n m hn_pos hm_pos
    have h3 : (n / m) * b + (n % m) * a ≥ 0 := by
      apply Int.add_nonneg
      · exact Int.mul_nonneg h3_parts.1 (by linarith)
      · exact Int.mul_nonneg h3_parts.2 (by linarith)
    exact min_nonneg_of_nonneg h1 h2 h3
  · -- Prove result = OptimalCost
    rfl
-- </vc-theorems>
