/-
You are given two images img1 and img2 both of size n x n, represented as binary, square matrices of the same size. (A binary matrix has only 0s and 1s as values.)
We translate one image however we choose (sliding it left, right, up, or down any number of units), and place it on top of the other image.  After, the overlap of this translation is the number of positions that have a 1 in both images.
(Note also that a translation does not include any kind of rotation.)
What is the largest possible overlap?

Example 1:

Input: img1 = [[1,1,0],[0,1,0],[0,1,0]], img2 = [[0,0,0],[0,1,1],[0,0,1]]
Output: 3
Explanation: We slide img1 to right by 1 unit and down by 1 unit.

The number of positions that have a 1 in both images is 3. (Shown in red)

Example 2:
Input: img1 = [[1]], img2 = [[1]]
Output: 1

Example 3:
Input: img1 = [[0]], img2 = [[0]]
Output: 0

Constraints:

n == img1.length
n == img1[i].length
n == img2.length 
n == img2[i].length
1 <= n <= 30
img1[i][j] is 0 or 1.
img2[i][j] is 0 or 1.
-/

-- <vc-helpers>
-- </vc-helpers>

def largest_overlap (img1 img2 : Matrix) : Nat :=
  sorry

theorem square_matrix_property 
  (n : Nat) (img1 img2 : Matrix)
  (h1 : img1.length = n)
  (h2 : img2.length = n) 
  (h3 : ∀ row, row ∈ img1 → row.length = n)
  (h4 : ∀ row, row ∈ img2 → row.length = n)
  (h5 : ∀ row ∈ img1, ∀ x ∈ row, x ≤ 1)
  (h6 : ∀ row ∈ img2, ∀ x ∈ row, x ≤ 1) :
  let result := largest_overlap img1 img2
  result ≥ 0 ∧ result ≤ n * n :=
sorry

theorem zero_overlap_property (n : Nat) (h : n > 0) :
  let ones_matrix := List.replicate n (List.replicate n 1)
  let zeros_matrix := List.replicate n (List.replicate n 0)
  largest_overlap ones_matrix zeros_matrix = 0 :=
sorry

theorem symmetry_property
  (n : Nat) (img1 img2 : Matrix)
  (h1 : img1.length = n)
  (h2 : img2.length = n)
  (h3 : ∀ row, row ∈ img1 → row.length = n)
  (h4 : ∀ row, row ∈ img2 → row.length = n)
  (h5 : ∀ row ∈ img1, ∀ x ∈ row, x ≤ 1)
  (h6 : ∀ row ∈ img2, ∀ x ∈ row, x ≤ 1) :
  largest_overlap img1 img2 = largest_overlap img2 img1 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval largest_overlap [[1, 1, 0], [0, 1, 0], [0, 1, 0]] [[0, 0, 0], [0, 1, 1], [0, 0, 1]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval largest_overlap [[1]] [[1]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval largest_overlap [[0]] [[0]]

-- Apps difficulty: interview
-- Assurance level: unguarded