import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  n ≥ 1

def MaxDistributions (n : Int) (h : ValidInput n) : Int :=
  if n % 3 = 0 then 2 * (n / 3) else 2 * (n / 3) + 1

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma max_distributions_positive (n : Int) (h : ValidInput n) : MaxDistributions n h ≥ 1 := by
  unfold MaxDistributions ValidInput at *
  split_ifs with h_mod
  · -- Case: n % 3 = 0
    have h_div : n / 3 ≥ 1 := by
      have : n ≥ 3 := by
        by_contra h_contra
        push_neg at h_contra
        have : n < 3 := h_contra
        have h_pos : (0 : Int) < 3 := by norm_num
        have : n % 3 < 3 := Int.emod_lt_of_pos n h_pos
        omega
      omega
    linarith
  · -- Case: n % 3 ≠ 0
    have h_nonneg : 0 ≤ n := by linarith [h]
    have h_div : n / 3 ≥ 0 := Int.ediv_nonneg h_nonneg (by norm_num : (0 : Int) ≤ 3)
    linarith
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  MaxDistributions n h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : Int) (h_precond : solve_precond n) : Prop :=
  result ≥ 1 ∧ result = MaxDistributions n h_precond

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · -- Prove result ≥ 1
    exact max_distributions_positive n h_precond
  · -- Prove result = MaxDistributions n h_precond
    rfl
-- </vc-theorems>
