def solve_subarrays (n : Nat) (arr : List Nat) : Nat :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def count_valid_subarrays (n : Nat) (arr : List Nat) : Nat :=
sorry

theorem solve_subarrays_singleton (x : Nat) :
  solve_subarrays 1 [x] = 0 :=
sorry

theorem solve_subarrays_alternating_nonneg (n : Nat) :
  let arr := List.replicate (2*n) 100000000 ++ List.replicate (2*n) 900000000
  solve_subarrays (4*n) arr ≥ 0 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_subarrays 3 [100000000, 900000000, 100000000]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_subarrays 1 [900000000]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_subarrays 2 [100000000, 100000000]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible