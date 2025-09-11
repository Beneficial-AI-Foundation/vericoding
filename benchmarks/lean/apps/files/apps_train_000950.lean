-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_good_rectangles (M N K : Nat) : Nat := sorry

theorem good_rectangles_positive (M N K : Nat) (h₁ : M > 0) (h₂ : N > 0) (h₃ : K > 0) :
  solve_good_rectangles M N K > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem good_rectangles_symmetric (M N K : Nat) :
  solve_good_rectangles M N K = solve_good_rectangles N M K := sorry

theorem good_rectangles_edge_case_k_gt_one (M N K : Nat) (h₁ : M = 1) (h₂ : N = 1) (h₃ : K > 1) :
  solve_good_rectangles M N K = 1 := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve_good_rectangles 1 3 1

/-
info: 9
-/
-- #guard_msgs in
-- #eval solve_good_rectangles 2 2 1

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_good_rectangles 1 1 2
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible