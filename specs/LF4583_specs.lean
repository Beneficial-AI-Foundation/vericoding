-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_black_cells (n m : Nat) : Nat := sorry

theorem count_black_cells_positive (n m : Nat) (hn : n > 0) (hm : m > 0) : 
  count_black_cells n m > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_black_cells_lower_bound (n m : Nat) (hn : n > 0) (hm : m > 0) :
  count_black_cells n m ≥ n + m - 1 := sorry

theorem count_black_cells_upper_bound (n m : Nat) (hn : n > 0) (hm : m > 0) :
  count_black_cells n m ≤ n * m := sorry

theorem count_black_cells_1x1 :
  count_black_cells 1 1 = 1 := sorry

theorem count_black_cells_symmetry (n m : Nat) (hn : n > 0) (hm : m > 0) :
  count_black_cells n m = count_black_cells m n := sorry
-- </vc-theorems>