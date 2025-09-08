/-
On an N x N grid, each square grid[i][j] represents the elevation at that point (i,j).

Now rain starts to fall. At time t, the depth of the water everywhere is t. You can swim from a square to another 4-directionally adjacent square if and only if the elevation of both squares individually are at most t. You can swim infinite distance in zero time. Of course, you must stay within the boundaries of the grid during your swim.

You start at the top left square (0, 0). What is the least time until you can reach the bottom right square (N-1, N-1)?

Example 1:

Input: [[0,2],[1,3]]
Output: 3
Explanation:
At time 0, you are in grid location (0, 0).
You cannot go anywhere else because 4-directionally adjacent neighbors have a higher elevation than t = 0.

You cannot reach point (1, 1) until time 3.
When the depth of water is 3, we can swim anywhere inside the grid.

Example 2:

Input: [[0,1,2,3,4],[24,23,22,21,5],[12,13,14,15,16],[11,17,18,19,20],[10,9,8,7,6]]
Output: 16
Explanation:
 0  1  2  3  4
24 23 22 21  5
12 13 14 15 16
11 17 18 19 20
10  9  8  7  6

The final route is marked in bold.
We need to wait until time 16 so that (0, 0) and (4, 4) are connected.

Note:

       2 <= N <= 50.
       grid[i][j] is a permutation of [0, ..., N*N - 1].
-/

def Matrix (α : Type) := List (List α)

def swim_time (grid : Matrix Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def can_reach (t : Nat) (grid : Matrix Nat) (i j : Nat) (visited : List (Nat × Nat)) : Bool := sorry

theorem swim_time_non_negative (grid : Matrix Nat) : 
  swim_time grid ≥ 0 := sorry

theorem swim_time_bounds {grid : Matrix Nat} (h : grid.length > 0) :
  swim_time grid ≥ (grid.head!.head!) ∧
  swim_time grid ≥ (grid.getLast!.getLast!) ∧
  swim_time grid ≤ grid.length * grid.length := sorry

theorem swim_time_monotonic {grid grid2 : Matrix Nat} {i j : Nat}
  (h1 : i < grid.length)
  (h2 : j < grid.length)
  (h3 : ∀ x y, x ≠ i ∨ y ≠ j → 
    (grid.get! x).get! y = (grid2.get! x).get! y)
  (h4 : (grid2.get! i).get! j = (grid.get! i).get! j + 1) :
  swim_time grid2 ≥ swim_time grid := sorry

theorem swim_time_path_exists (grid : Matrix Nat) : 
  can_reach (swim_time grid) grid 0 0 [] = true := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval swim_time [[0, 2], [1, 3]]

/-
info: 16
-/
-- #guard_msgs in
-- #eval swim_time [[0, 1, 2, 3, 4], [24, 23, 22, 21, 5], [12, 13, 14, 15, 16], [11, 17, 18, 19, 20], [10, 9, 8, 7, 6]]

/-
info: 3
-/
-- #guard_msgs in
-- #eval swim_time [[0, 1], [2, 3]]

-- Apps difficulty: interview
-- Assurance level: unguarded