-- <vc-helpers>
-- </vc-helpers>

def solve_QC_parity (n : Nat) (k : Nat) : Nat :=
  sorry

theorem solve_QC_parity_binary (n k : Nat) (h : k ≤ n) :
  solve_QC_parity n k = 0 ∨ solve_QC_parity n k = 1 :=
  sorry

theorem solve_QC_parity_single (n : Nat) (h : n > 0) :
  solve_QC_parity n 1 = 1 :=
  sorry

theorem solve_QC_parity_full (n : Nat) (h : n > 0) :
  solve_QC_parity n n = 1 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_QC_parity 4 2

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_QC_parity 5 2

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_QC_parity 6 3

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible