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
-- LLM HELPER
lemma int_mod_nonneg_of_pos (n m : Int) (hm_pos : 0 < m) : 0 ≤ n % m := by
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  simpa using Int.emod_nonneg n hm_ne

-- LLM HELPER
lemma int_mod_lt_of_pos (n m : Int) (hm_pos : 0 < m) : n % m < m := by
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  simpa [abs_of_pos hm_pos] using Int.emod_lt n hm_ne

-- LLM HELPER
lemma minCost_nonneg (n m a b : Int) (h : ValidInput n m a b) : 0 ≤ MinCostToDivisible n m a b := by
  -- extract hypotheses
  have hm_ge_one : 1 ≤ m := by
    simpa [ValidInput] using h.2.1
  have ha_ge_one : 1 ≤ a := by
    simpa [ValidInput] using h.2.2.1
  have hb_ge_one : 1 ≤ b := by
    simpa [ValidInput] using h.2.2.2
  -- basic facts
  have h01 : (0 : Int) ≤ 1 := by decide
  have h01lt : (0 : Int) < 1 := by decide
  have hm_pos : 0 < m := lt_of_lt_of_le h01lt hm_ge_one
  have ha_nonneg : 0 ≤ a := le_trans h01 ha_ge_one
  have hb_nonneg : 0 ≤ b := le_trans h01 hb_ge_one
  -- define k and collect bounds
  set k := n % m with hk
  have hk_nonneg : 0 ≤ k := by
    simpa [hk] using int_mod_nonneg_of_pos n m hm_pos
  have hk_lt_m : k < m := by
    simpa [hk] using int_mod_lt_of_pos n m hm_pos
  have hmk_nonneg : 0 ≤ m - k := sub_nonneg.mpr (le_of_lt hk_lt_m)
  have h_kb_nonneg : 0 ≤ k * b := mul_nonneg hk_nonneg hb_nonneg
  have h_mk_a_nonneg : 0 ≤ (m - k) * a := mul_nonneg hmk_nonneg ha_nonneg
  -- finish by case split on the if
  have h' : 0 ≤ (if k * b < (m - k) * a then k * b else (m - k) * a) := by
    by_cases hlt : k * b < (m - k) * a
    · simpa [hlt] using h_kb_nonneg
    · simpa [hlt] using h_mk_a_nonneg
  simpa [MinCostToDivisible, hk] using h'
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
  constructor
  · simp [solve, solve_postcond]
  · have hvalid : ValidInput n m a b := by simpa [solve_precond] using h_precond
    simpa [solve, solve_postcond] using minCost_nonneg n m a b hvalid
-- </vc-theorems>
