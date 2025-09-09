/-
Given an n x n binary grid, in one step you can choose two adjacent rows of the grid and swap them.
A grid is said to be valid if all the cells above the main diagonal are zeros.
Return the minimum number of steps needed to make the grid valid, or -1 if the grid cannot be valid.
The main diagonal of a grid is the diagonal that starts at cell (1, 1) and ends at cell (n, n).

Example 1:

Input: grid = [[0,0,1],[1,1,0],[1,0,0]]
Output: 3

Example 2:

Input: grid = [[0,1,1,0],[0,1,1,0],[0,1,1,0],[0,1,1,0]]
Output: -1
Explanation: All rows are similar, swaps have no effect on the grid.

Example 3:

Input: grid = [[1,0,0],[1,1,0],[1,1,1]]
Output: 0

Constraints:

n == grid.length
n == grid[i].length
1 <= n <= 200
grid[i][j] is 0 or 1
-/

-- <vc-helpers>
-- </vc-helpers>

def minSwaps (grid : List (List Nat)) : Int := sorry

def isValidFinalGrid (grid : List (List Nat)) : Bool := sorry

theorem identity_matrix_no_swaps {n : Nat} (grid : List (List Nat))
  (h : grid = List.map (fun i => List.map (fun j => if i = j then 1 else 0) (List.range n)) (List.range n)) :
  minSwaps grid = 0 := sorry

theorem impossible_grid_negative_one {n : Nat} (grid : List (List Nat)) 
  (h : grid = List.replicate n (List.replicate n 1)) :
  minSwaps grid = -1 := sorry

theorem valid_result_grid_property (grid : List (List Nat))
  (h1 : grid ≠ [])
  (h2 : ∀ row ∈ grid, row ≠ [])
  (h3 : ∀ row ∈ grid, row.length = grid.length)
  (h4 : minSwaps grid ≥ 0) :
  isValidFinalGrid grid := sorry

theorem result_is_minimal (grid : List (List Nat))
  (h1 : grid ≠ [])
  (h2 : ∀ row ∈ grid, row ≠ [])
  (h3 : ∀ row ∈ grid, row.length = grid.length)
  (h4 : minSwaps grid ≥ 0) :
  minSwaps grid ≤ (grid.length * (grid.length - 1)) / 2 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval minSwaps [[0, 0, 1], [1, 1, 0], [1, 0, 0]]

/-
info: -1
-/
-- #guard_msgs in
-- #eval minSwaps [[0, 1, 1, 0], [0, 1, 1, 0], [0, 1, 1, 0], [0, 1, 1, 0]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval minSwaps [[1, 0, 0], [1, 1, 0], [1, 1, 1]]

-- Apps difficulty: interview
-- Assurance level: unguarded