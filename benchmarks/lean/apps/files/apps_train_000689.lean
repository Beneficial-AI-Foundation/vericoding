-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_matrix_product (n : Nat) (a : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_matrix_product_bounds (n : Nat) (a : Nat) :
  n ≥ 1 → 0 ≤ solve_matrix_product n a ∧ solve_matrix_product n a < 10^9+7 :=
sorry

theorem solve_matrix_product_zero (n : Nat) :
  n ≥ 1 → solve_matrix_product n 0 = 0 := 
sorry

theorem solve_matrix_product_single_step (a : Nat) :
  solve_matrix_product 1 a = a % (10^9+7) :=
sorry

/-
info: 511620149
-/
-- #guard_msgs in
-- #eval solve_matrix_product 3 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_matrix_product 1 2

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_matrix_product 5 0
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible