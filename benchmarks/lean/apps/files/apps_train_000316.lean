/-
Given an N x N grid containing only values 0 and 1, where 0 represents water and 1 represents land, find a water cell such that its distance to the nearest land cell is maximized and return the distance.
The distance used in this problem is the Manhattan distance: the distance between two cells (x0, y0) and (x1, y1) is |x0 - x1| + |y0 - y1|.
If no land or water exists in the grid, return -1.

Example 1:

Input: [[1,0,1],[0,0,0],[1,0,1]]
Output: 2
Explanation: 
The cell (1, 1) is as far as possible from all the land with distance 2.

Example 2:

Input: [[1,0,0],[0,0,0],[0,0,0]]
Output: 4
Explanation: 
The cell (2, 2) is as far as possible from all the land with distance 4.

Note:

1 <= grid.length == grid[0].length <= 100
grid[i][j] is 0 or 1
-/

def maxDistance (grid : List (List Int)) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def rotateGrid (grid : List (List Int)) : List (List Int) :=
  sorry

theorem maxDistance_bounds (grid : List (List Int)) : 
  let result := maxDistance grid
  result ≥ -1 ∧ (result ≠ -1 → result ≤ 2 * grid.length) :=
sorry

theorem maxDistance_all_water (grid : List (List Int)) :
  (∀ row ∈ grid, ∀ cell ∈ row, cell = 0) → 
  maxDistance grid = -1 :=
sorry

theorem maxDistance_all_land (grid : List (List Int)) :
  (∀ row ∈ grid, ∀ cell ∈ row, cell = 1) → 
  maxDistance grid = -1 :=
sorry 

theorem maxDistance_rotation {grid : List (List Int)} :
  maxDistance grid = maxDistance (rotateGrid grid) :=
sorry

theorem maxDistance_edge_cases :
  maxDistance [[1]] = -1 ∧
  maxDistance [[0]] = -1 ∧
  maxDistance [[1,0],[0,0]] = 2 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval maxDistance [[1, 0, 1], [0, 0, 0], [1, 0, 1]]

/-
info: 4
-/
-- #guard_msgs in
-- #eval maxDistance [[1, 0, 0], [0, 0, 0], [0, 0, 0]]

/-
info: -1
-/
-- #guard_msgs in
-- #eval maxDistance [[0, 0, 0], [0, 0, 0], [0, 0, 0]]

-- Apps difficulty: interview
-- Assurance level: unguarded