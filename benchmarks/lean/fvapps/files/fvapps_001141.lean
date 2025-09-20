-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_pool_shots (N K x y : Nat) : Nat × Nat := sorry

theorem solve_pool_shots_bounds 
  (N K x y : Nat) (h1 : x ≤ N) (h2 : y ≤ N) :
  let (rx, ry) := solve_pool_shots N K x y
  rx ≤ N ∧ ry ≤ N := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_pool_shots_boundary 
  (N K x y : Nat) (h1 : x ≤ N) (h2 : y ≤ N) (h3 : x ≠ y) :
  let (rx, ry) := solve_pool_shots N K x y
  rx = 0 ∨ rx = N ∨ ry = 0 ∨ ry = N := sorry

theorem solve_pool_shots_cycle
  (N K x y : Nat) (h1 : x ≤ N) (h2 : y ≤ N) :
  solve_pool_shots N K x y = solve_pool_shots N (K + 4) x y := sorry

theorem solve_pool_shots_equal_pos
  (N K pos : Nat) (h : pos ≤ N) :
  solve_pool_shots N K pos pos = (N, N) := sorry
-- </vc-theorems>