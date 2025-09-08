/-
In an n*n grid, there is a snake that spans 2 cells and starts moving from the top left corner at (0, 0) and (0, 1). The grid has empty cells represented by zeros and blocked cells represented by ones. The snake wants to reach the lower right corner at (n-1, n-2) and (n-1, n-1).
In one move the snake can:

Move one cell to the right if there are no blocked cells there. This move keeps the horizontal/vertical position of the snake as it is.
Move down one cell if there are no blocked cells there. This move keeps the horizontal/vertical position of the snake as it is.
Rotate clockwise if it's in a horizontal position and the two cells under it are both empty. In that case the snake moves from (r, c) and (r, c+1) to (r, c) and (r+1, c).

Rotate counterclockwise if it's in a vertical position and the two cells to its right are both empty. In that case the snake moves from (r, c) and (r+1, c) to (r, c) and (r, c+1).

Return the minimum number of moves to reach the target.
If there is no way to reach the target, return -1.

Example 1:

Input: grid = [[0,0,0,0,0,1],
               [1,1,0,0,1,0],
               [0,0,0,0,1,1],
               [0,0,1,0,1,0],
               [0,1,1,0,0,0],
               [0,1,1,0,0,0]]
Output: 11
Explanation:
One possible solution is [right, right, rotate clockwise, right, down, down, down, down, rotate counterclockwise, right, down].

Example 2:
Input: grid = [[0,0,1,1,1,1],
               [0,0,0,0,1,1],
               [1,1,0,0,0,1],
               [1,1,1,0,0,1],
               [1,1,1,0,0,1],
               [1,1,1,0,0,0]]
Output: 9

Constraints:

2 <= n <= 100
0 <= grid[i][j] <= 1
It is guaranteed that the snake starts at empty cells.
-/

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