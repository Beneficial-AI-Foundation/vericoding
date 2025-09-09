-- <vc-helpers>
-- </vc-helpers>

def solve (n : Nat) : Nat :=
  sorry

theorem solve_non_negative (n : Nat) (h : n ≥ 1) : 
  solve n ≥ 0 := 
  sorry

theorem solve_formula (n : Nat) (h : n ≥ 1) :
  solve n = ((n-1)*n)/2 :=
  sorry

theorem solve_monotonic (n : Nat) (h : n ≥ 2) :
  solve n > solve (n-1) :=
  sorry

theorem solve_base_case_one : 
  solve 1 = 0 :=
  sorry

theorem solve_base_case_two :
  solve 2 = 1 :=
  sorry

/-
info: 21
-/
-- #guard_msgs in
-- #eval solve 7

/-
info: 36
-/
-- #guard_msgs in
-- #eval solve 9

/-
info: 10
-/
-- #guard_msgs in
-- #eval solve 5

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible