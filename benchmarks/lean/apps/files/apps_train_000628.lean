-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_random_generator (n s : Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_random_generator_range (n s : Nat) :
  solve_random_generator n s ≥ -1 := 
sorry

theorem solve_random_generator_n1 (s : Nat) :
  solve_random_generator 1 s = s := 
sorry

theorem solve_random_generator_n2 (s : Nat) :
  s > 1 → solve_random_generator 2 s = s - 1 :=
sorry

theorem solve_random_generator_n_gt_2 (n s : Nat) :
  n > 2 → s > 1 → solve_random_generator n s = 0 :=
sorry

theorem solve_random_generator_invalid (n s : Nat) :
  s ≤ 1 → n > 1 → solve_random_generator n s = -1 :=
sorry

theorem solve_random_generator_edge_cases :
  solve_random_generator 1 0 = 0 ∧ 
  solve_random_generator 2 1 = -1 ∧
  solve_random_generator 10 1 = -1 :=
sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve_random_generator 1 5

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_random_generator 2 2

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_random_generator 3 5
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible