-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_square_plots (length width : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_square_plots_positive (length width : Nat) (h1 : length > 0) (h2 : width > 0) :
  min_square_plots length width > 0 :=
  sorry

theorem min_square_plots_symmetric (length width : Nat) (h1 : length > 0) (h2 : width > 0) : 
  min_square_plots length width = min_square_plots width length :=
  sorry

theorem min_square_plots_double_dims (length width : Nat) (h1 : length > 0) (h2 : width > 0) :
  min_square_plots (2 * length) (2 * width) = min_square_plots length width :=
  sorry

theorem min_square_plots_equal_dims (n : Nat) (h : n > 0) :
  min_square_plots n n = 1 :=
  sorry
-- </vc-theorems>