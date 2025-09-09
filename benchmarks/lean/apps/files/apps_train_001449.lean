-- <vc-helpers>
-- </vc-helpers>

def min_square_plots (length width : Nat) : Nat :=
  sorry

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

/-
info: 6
-/
-- #guard_msgs in
-- #eval min_square_plots 10 15

/-
info: 6
-/
-- #guard_msgs in
-- #eval min_square_plots 4 6

/-
info: 6
-/
-- #guard_msgs in
-- #eval min_square_plots 100 150

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible