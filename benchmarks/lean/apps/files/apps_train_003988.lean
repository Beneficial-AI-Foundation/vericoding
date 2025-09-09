-- <vc-helpers>
-- </vc-helpers>

def sum_cubes (n : Nat) : Nat := sorry

theorem sum_cubes_positive (n : Nat) (h : n > 0) : 
  sum_cubes n > 0 :=
sorry

theorem sum_cubes_greater_eq_n (n : Nat) (h : n > 0) :
  sum_cubes n ≥ n :=
sorry

theorem sum_cubes_strictly_increasing (n : Nat) (h : n > 0) :
  sum_cubes (n + 1) > sum_cubes n :=
sorry

theorem sum_cubes_base_case_one :
  sum_cubes 1 = 1 :=
sorry

theorem sum_cubes_base_case_two :
  sum_cubes 2 = 9 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval sum_cubes 1

/-
info: 9
-/
-- #guard_msgs in
-- #eval sum_cubes 2

/-
info: 36
-/
-- #guard_msgs in
-- #eval sum_cubes 3

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible