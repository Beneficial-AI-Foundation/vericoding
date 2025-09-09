-- <vc-helpers>
-- </vc-helpers>

def solve_candy_boxes (C: List Nat) (n: Nat) (x: Nat) : Nat × Nat := sorry

theorem specific_input_case_1 :
  solve_candy_boxes [1] 1 1 = (1, 0) := sorry

theorem specific_input_case_2 :
  solve_candy_boxes [1, 1] 2 1 = (1, 1) := sorry

/-
info: (4, 1)
-/
-- #guard_msgs in
-- #eval solve_candy_boxes [2, 8, 8, 2, 9] 5 2

/-
info: (1, 0)
-/
-- #guard_msgs in
-- #eval solve_candy_boxes [5] 1 3

/-
info: (1, 1)
-/
-- #guard_msgs in
-- #eval solve_candy_boxes [2, 2] 2 1

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible