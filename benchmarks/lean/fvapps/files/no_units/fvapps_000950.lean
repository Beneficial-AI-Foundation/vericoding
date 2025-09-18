-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>