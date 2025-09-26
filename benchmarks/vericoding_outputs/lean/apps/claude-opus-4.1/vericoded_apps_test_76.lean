import Mathlib
-- <vc-preamble>
def ValidInput (n m a b : Int) : Prop :=
  n ≥ 1 ∧ m ≥ 1 ∧ a ≥ 1 ∧ b ≥ 1

def MinCostToDivisible (n m a b : Int) : Int :=
  let k := n % m
  if k * b < (m - k) * a then k * b else (m - k) * a

@[reducible, simp]
def solve_precond (n m a b : Int) : Prop :=
  ValidInput n m a b
-- </vc-preamble>

-- <vc-helpers>
-- Helper lemmas for the main proof
lemma mod_bounds (n m : Int) (hm : m ≥ 1) : 0 ≤ n % m ∧ n % m < m := by
  have h1 := Int.emod_nonneg n (by omega : m ≠ 0)
  have h2 := Int.emod_lt_of_pos n (by omega : 0 < m)
  exact ⟨h1, h2⟩

lemma min_cost_nonneg (n m a b : Int) (h : ValidInput n m a b) : MinCostToDivisible n m a b ≥ 0 := by
  unfold MinCostToDivisible
  have ⟨_, hm, ha, hb⟩ := h
  have ⟨hk_nonneg, hk_lt⟩ := mod_bounds n m hm
  -- Work directly with the let-binding structure
  show (let k := n % m; if k * b < (m - k) * a then k * b else (m - k) * a) ≥ 0
  -- Now we can split on the condition
  by_cases h_cond : (n % m) * b < (m - (n % m)) * a
  · simp [h_cond]
    exact Int.mul_nonneg hk_nonneg (by omega : b ≥ 0)
  · simp [h_cond]
    have hmk : m - n % m ≥ 0 := by omega
    exact Int.mul_nonneg hmk (by omega : a ≥ 0)
-- </vc-helpers>

-- <vc-definitions>
def solve (n m a b : Int) (h_precond : solve_precond n m a b) : Int :=
  MinCostToDivisible n m a b
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m a b : Int) (result : Int) (h_precond : solve_precond n m a b) : Prop :=
  result = MinCostToDivisible n m a b ∧ result ≥ 0

theorem solve_spec_satisfied (n m a b : Int) (h_precond : solve_precond n m a b) :
    solve_postcond n m a b (solve n m a b h_precond) h_precond := by
  unfold solve_postcond solve MinCostToDivisible
  have h := h_precond
  unfold solve_precond ValidInput at h
  constructor
  · rfl
  · exact min_cost_nonneg n m a b h
-- </vc-theorems>
