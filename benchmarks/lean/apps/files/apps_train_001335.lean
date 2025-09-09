-- <vc-helpers>
-- </vc-helpers>

def solve_grid_probability (n m : Nat) : Float := sorry

theorem solve_grid_probability_positive (n m : Nat) 
  (h1 : n > 0) (h2 : m > 0) : 
  solve_grid_probability n m > 0 := sorry

theorem solve_grid_probability_sum (n m : Nat)
  (h1 : n > 0) (h2 : m > 0) :
  (solve_grid_probability n m - Float.ofNat (n + m - 1)).abs < 0.000001 := sorry

theorem solve_grid_probability_symmetry (n m : Nat)
  (h1 : n > 0) (h2 : m > 0) :
  (solve_grid_probability n m - solve_grid_probability m n).abs < 0.000001 := sorry

theorem solve_grid_probability_one_one :
  (solve_grid_probability 1 1 - 1).abs < 0.000001 := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible