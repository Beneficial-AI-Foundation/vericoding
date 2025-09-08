/-
Given a rows * columns matrix mat of ones and zeros, return how many submatrices have all ones.

Example 1:
Input: mat = [[1,0,1],
              [1,1,0],
              [1,1,0]]
Output: 13
Explanation:
There are 6 rectangles of side 1x1.
There are 2 rectangles of side 1x2.
There are 3 rectangles of side 2x1.
There is 1 rectangle of side 2x2. 
There is 1 rectangle of side 3x1.
Total number of rectangles = 6 + 2 + 3 + 1 + 1 = 13.

Example 2:
Input: mat = [[0,1,1,0],
              [0,1,1,1],
              [1,1,1,0]]
Output: 24
Explanation:
There are 8 rectangles of side 1x1.
There are 5 rectangles of side 1x2.
There are 2 rectangles of side 1x3. 
There are 4 rectangles of side 2x1.
There are 2 rectangles of side 2x2. 
There are 2 rectangles of side 3x1. 
There is 1 rectangle of side 3x2. 
Total number of rectangles = 8 + 5 + 2 + 4 + 2 + 2 + 1 = 24.

Example 3:
Input: mat = [[1,1,1,1,1,1]]
Output: 21

Example 4:
Input: mat = [[1,0,1],[0,1,0],[1,0,1]]
Output: 5

Constraints:

1 <= rows <= 150
1 <= columns <= 150
0 <= mat[i][j] <= 1
-/

-- <vc-helpers>
-- </vc-helpers>

def count_submatrices (matrix : Matrix Int) : Nat :=
  sorry

theorem count_submatrices_nonnegative (matrix : Matrix Int) :
  count_submatrices matrix ≥ 0 := sorry

theorem count_submatrices_at_least_ones (matrix : Matrix Int) :
  count_submatrices matrix ≥ ((matrix.data).join.filter (· = 1)).length := sorry

theorem count_submatrices_all_zeros (matrix : Matrix Int) :
  ((matrix.data).all (fun row => row.all (fun x => x = 0))) → count_submatrices matrix = 0 := sorry

theorem count_submatrices_all_ones {n m : Nat} (matrix : Matrix Int) 
  (h1 : (matrix.data).length = n)
  (h2 : ∀ row ∈ matrix.data, row.length = m)
  (h3 : (matrix.data).all (fun row => row.all (fun x => x = 1))) :
  count_submatrices matrix = n * m * (n * m + 1) / 2 := sorry

theorem count_submatrices_single_row_ones (n : Nat) :
  count_submatrices ⟨[List.replicate n 1]⟩ = n * (n + 1) / 2 := sorry

theorem count_submatrices_single_col_ones (n : Nat) :
  count_submatrices ⟨List.replicate n [1]⟩ = n * (n + 1) / 2 := sorry

/-
info: 13
-/
-- #guard_msgs in
-- #eval count_submatrices [[1, 0, 1], [1, 1, 0], [1, 1, 0]]

/-
info: 24
-/
-- #guard_msgs in
-- #eval count_submatrices [[0, 1, 1, 0], [0, 1, 1, 1], [1, 1, 1, 0]]

/-
info: 21
-/
-- #guard_msgs in
-- #eval count_submatrices [[1, 1, 1, 1, 1, 1]]

-- Apps difficulty: interview
-- Assurance level: unguarded