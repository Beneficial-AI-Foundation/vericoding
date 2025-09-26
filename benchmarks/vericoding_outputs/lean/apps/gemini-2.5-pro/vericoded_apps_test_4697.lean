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

-- LLM HELPER
private lemma MaxSccGroups_nonneg (n m : Int) (h : ValidInput n m) : MaxSccGroups n m h ≥ 0 := by
  unfold MaxSccGroups
  dsimp only
  split_ifs with h_if
  · -- case n < m / 2
    have hn : 0 ≤ n := h.1
    have h_rem_nonneg : 0 ≤ m - n * 2 := by
      have h_le_div : n + 1 ≤ m / 2 := Int.add_one_le_of_lt h_if
      have hc : 0 < (2 : Int) := by decide
      have h' := (Int.le_ediv_iff_mul_le hc).mp h_le_div
      linarith
    have h_add_nonneg : 0 ≤ (m - n * 2) / 4 := Int.ediv_nonneg h_rem_nonneg (by decide)
    exact Int.add_nonneg hn h_add_nonneg
  · -- case ¬(n < m / 2)
    have hm : 0 ≤ m := h.2
    have h_direct_nonneg : 0 ≤ m / 2 := Int.ediv_nonneg hm (by decide)
    have h_rem_nonneg : 0 ≤ m - m / 2 * 2 :=
      Int.sub_nonneg_of_le (Int.ediv_mul_le m (by decide))
    have h_add_nonneg : 0 ≤ (m - m / 2 * 2) / 4 := Int.ediv_nonneg h_rem_nonneg (by decide)
    exact Int.add_nonneg h_direct_nonneg h_add_nonneg
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
  constructor
  · exact MaxSccGroups_nonneg n m h_precond
  · rfl
-- </vc-theorems>
