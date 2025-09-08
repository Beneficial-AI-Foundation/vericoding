/-
A 3 x 3 magic square is a 3 x 3 grid filled with distinct numbers from 1 to 9 such that each row, column, and both diagonals all have the same sum.
Given a row x col grid of integers, how many 3 x 3 "magic square" subgrids are there?  (Each subgrid is contiguous).

Example 1:

Input: grid = [[4,3,8,4],[9,5,1,9],[2,7,6,2]]
Output: 1
Explanation: 
The following subgrid is a 3 x 3 magic square:

while this one is not:

In total, there is only one magic square inside the given grid.

Example 2:
Input: grid = [[8]]
Output: 0

Example 3:
Input: grid = [[4,4],[3,3]]
Output: 0

Example 4:
Input: grid = [[4,7,8],[9,5,1],[2,3,6]]
Output: 0

Constraints:

row == grid.length
col == grid[i].length
1 <= row, col <= 10
0 <= grid[i][j] <= 15
-/

-- <vc-helpers>
-- </vc-helpers>

def numMagicSquaresInside (grid : List (List Int)) : Int := sorry
def isMagicSquare (square : List (List Int)) : Bool := sorry

theorem numMagicSquaresInside_small_grid
  (grid : List (List Int))
  (h1 : grid.length < 3 ∨ grid.head!.length < 3) :
  numMagicSquaresInside grid = 0 := sorry

theorem isMagicSquare_returns_bool (square : List (List Int)) :
  isMagicSquare square = true ∨ isMagicSquare square = false := sorry

theorem isMagicSquare_invalid_range
  (square : List (List Int))
  (h1 : ∃ x, x ∈ square.join ∧ (x > 9 ∨ x < 1)) : 
  isMagicSquare square = false := sorry

theorem numMagicSquaresInside_empty_grid
  (rows cols : Nat)
  (h1 : rows ≥ 3)
  (h2 : cols ≥ 3) :
  numMagicSquaresInside (List.replicate rows (List.replicate cols 0)) ≥ 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval numMagicSquaresInside [[4, 3, 8, 4], [9, 5, 1, 9], [2, 7, 6, 2]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval numMagicSquaresInside [[8]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval numMagicSquaresInside [[4, 7, 8], [9, 5, 1], [2, 3, 6]]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible