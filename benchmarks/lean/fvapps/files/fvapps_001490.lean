-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_QC_parity (n : Nat) (k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_QC_parity_binary (n k : Nat) (h : k ≤ n) :
  solve_QC_parity n k = 0 ∨ solve_QC_parity n k = 1 :=
  sorry

theorem solve_QC_parity_single (n : Nat) (h : n > 0) :
  solve_QC_parity n 1 = 1 :=
  sorry

theorem solve_QC_parity_full (n : Nat) (h : n > 0) :
  solve_QC_parity n n = 1 :=
  sorry
-- </vc-theorems>