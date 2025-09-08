/-
Given N, consider a convex N-sided polygon with vertices labelled A[0], A[i], ..., A[N-1] in clockwise order.
Suppose you triangulate the polygon into N-2 triangles.  For each triangle, the value of that triangle is the product of the labels of the vertices, and the total score of the triangulation is the sum of these values over all N-2 triangles in the triangulation.
Return the smallest possible total score that you can achieve with some triangulation of the polygon.

Example 1:
Input: [1,2,3]
Output: 6
Explanation: The polygon is already triangulated, and the score of the only triangle is 6.

Example 2:

Input: [3,7,4,5]
Output: 144
Explanation: There are two triangulations, with possible scores: 3*7*5 + 4*5*7 = 245, or 3*4*5 + 3*4*7 = 144.  The minimum score is 144.

Example 3:
Input: [1,3,1,4,1,5]
Output: 13
Explanation: The minimum score triangulation has score 1*1*3 + 1*1*4 + 1*1*5 + 1*1*1 = 13.

Note:

3 <= A.length <= 50
1 <= A[i] <= 100
-/

-- <vc-helpers>
-- </vc-helpers>

def min_score_triangulation (vertices : List Nat) : Nat := sorry

theorem min_score_triangulation_nonnegative (vertices : List Nat) 
  (h: vertices.length ≥ 3) : 
  min_score_triangulation vertices ≥ 0 := sorry

theorem min_score_triangulation_triangle (a b c : Nat) :
  min_score_triangulation [a, b, c] = a * b * c := sorry

theorem min_score_triangulation_cyclic_invariant (vertices : List Nat) 
  (h: vertices.length ≥ 3) :
  min_score_triangulation vertices = 
  min_score_triangulation (vertices.tail ++ [vertices.head!]) := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval min_score_triangulation [1, 2, 3]

/-
info: 144
-/
-- #guard_msgs in
-- #eval min_score_triangulation [3, 7, 4, 5]

/-
info: 13
-/
-- #guard_msgs in
-- #eval min_score_triangulation [1, 3, 1, 4, 1, 5]

-- Apps difficulty: interview
-- Assurance level: unguarded