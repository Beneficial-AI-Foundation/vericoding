import Mathlib
-- <vc-preamble>
def ValidInput (n m : Int) : Prop :=
  n ≥ 0 ∧ m ≥ 0

def MaxSccGroups (n m : Int) (h : ValidInput n m) : Int :=
  let directGroups := if n < m / 2 then n else m / 2
  let remainingCPieces := m - directGroups * 2
  let additionalGroups := remainingCPieces / 4
  directGroups + additionalGroups

@[reducible, simp]
def solve_precond (n m : Int) : Prop :=
  ValidInput n m
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Lemmas for the correctness proof
lemma max_scc_groups_nonneg (n m : Int) (h : ValidInput n m) : MaxSccGroups n m h ≥ 0 := by
  unfold MaxSccGroups
  simp only [ValidInput] at h
  have hn_nonneg : n ≥ 0 := h.1
  have hm_nonneg : m ≥ 0 := h.2
  have h_direct_nonneg : (if n < m / 2 then n else m / 2) ≥ 0 := by
    split_ifs with h_cond
    · exact hn_nonneg
    · apply Int.ediv_nonneg
      · exact hm_nonneg
      · norm_num
  have h_additional_nonneg : (m - (if n < m / 2 then n else m / 2) * 2) / 4 ≥ 0 := by
    apply Int.ediv_nonneg
    · simp only [Int.sub_nonneg]
      split_ifs with h_cond
      · have : n ≤ m / 2 := Int.le_of_lt h_cond
        have : n * 2 ≤ (m / 2) * 2 := Int.mul_le_mul_of_nonneg_right this (by norm_num)
        have : (m / 2) * 2 ≤ m := Int.ediv_mul_le m (by norm_num)
        linarith
      · have : m / 2 * 2 ≤ m := Int.ediv_mul_le m (by norm_num)
        linarith
    · norm_num
  linarith
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (h_precond : solve_precond n m) : Int :=
  MaxSccGroups n m h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (result : Int) (h_precond : solve_precond n m) : Prop :=
  result ≥ 0 ∧ result = MaxSccGroups n m h_precond

theorem solve_spec_satisfied (n m : Int) (h_precond : solve_precond n m) :
    solve_postcond n m (solve n m h_precond) h_precond := by
  unfold solve_postcond solve
  simp only [solve_precond] at h_precond
  constructor
  · exact max_scc_groups_nonneg n m h_precond
  · rfl
-- </vc-theorems>
