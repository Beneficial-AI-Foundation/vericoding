-- <vc-helpers>
-- </vc-helpers>

def minimum_moves (grid : Array (Array Nat)) : Int := sorry

/- For any non-empty n×n grid with all zeros, there exists a valid path to reach bottom right -/

theorem min_moves_empty_grid_reaches {n : Nat} (h : n ≥ 3) :
  let grid := Array.mk (List.replicate n (Array.mk (List.replicate n (0:Nat))))
  minimum_moves grid > 0 := sorry

/- For any n×n grid that is blocked except start position, no valid path exists -/

theorem min_moves_blocked_grid_unreachable {n : Nat} (h : n ≥ 3) :
  let blockedGrid := Array.mk (List.replicate n (Array.mk (List.replicate n (1:Nat))))
  let grid := blockedGrid.set! 0 (blockedGrid[0]!.set! 0 0) |>.set! 0 (blockedGrid[0]!.set! 1 0)
  minimum_moves grid = -1 := sorry

/- For minimal 3×3 grid of all zeros, there exists a valid path -/

theorem min_moves_minimal_grid_reaches :
  let grid := Array.mk [Array.mk [(0:Nat),(0:Nat),(0:Nat)], Array.mk [(0:Nat),(0:Nat),(0:Nat)], Array.mk [(0:Nat),(0:Nat),(0:Nat)]]
  minimum_moves grid > 0 := sorry

/-
info: 11
-/
-- #guard_msgs in
-- #eval minimum_moves #[[0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 1, 0], [0, 0, 0, 0, 1, 1], [0, 0, 1, 0, 1, 0], [0, 1, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0]]

/-
info: 9
-/
-- #guard_msgs in
-- #eval minimum_moves #[[0, 0, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1], [1, 1, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1], [1, 1, 1, 0, 0, 1], [1, 1, 1, 0, 0, 0]]

-- Apps difficulty: interview
-- Assurance level: unguarded