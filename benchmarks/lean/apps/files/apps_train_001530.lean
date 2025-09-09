/-
Chef likes problems on geometry a lot. Please help him to solve one such problem.
Find all possible triangles with integer sides which has the radius of inscribed circle (also known as incircle) equal to R.
Two triangles are said to be different if they have at least one different side lengths. Formally, let there be two triangles T1, T2. Let a, b, c denote the sides of triangle T1, such that a ≤ b ≤ c. Similarly, Let d, e, f denote the sides of triangle T2, such that d ≤ e ≤ f. Then T1 will said to be different from T2 if either a ≠ d, or b ≠ e or c ≠ f.

-----Input-----
There is a single test case per test file.
The only line of input contains an integer R.

-----Output-----
Output in first line single number - number of triangles satisfying statement.
Order the sides of triangles in non-decreasing order. Output all triangles in non-decreasing order, i.e. order first by smallest sides, otherwise by second smallest sides, if first and second sides equal, then by third.

-----Constraints-----
- 1 ≤ R ≤ 100 

-----Subtasks-----
- Subtask #1: (20 points)  1 ≤ R ≤ 3
- Subtask #2: (30 points)  1 ≤ R ≤ 20
- Subtask #3: (50 points)  Original constraints

-----Example-----
Input:2

Output:5
5 12 13
6 8 10
6 25 29
7 15 20
9 10 17
-/

-- <vc-helpers>
-- </vc-helpers>

def find_triangles_with_incircle (r : Nat) : List (List Nat) := sorry

theorem r1_triangles (r : Nat) :
  r = 1 → find_triangles_with_incircle r = [[3,4,5]] := sorry

theorem r2_triangles (r : Nat) :
  r = 2 → find_triangles_with_incircle r = [[5,12,13], [6,8,10], [6,25,29], [7,15,20], [9,10,17]] := sorry 

theorem zero_radius :
  find_triangles_with_incircle 0 = [] := sorry

theorem result_count_r1 (r : Nat) :
  r = 1 → List.length (find_triangles_with_incircle r) = 1 := sorry

theorem result_count_r2 (r : Nat) :
  r = 2 → List.length (find_triangles_with_incircle r) = 5 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval len find_triangles_with_incircle(2)

/-
info: 1
-/
-- #guard_msgs in
-- #eval len find_triangles_with_incircle(1)

/-
info: 13
-/
-- #guard_msgs in
-- #eval len find_triangles_with_incircle(3)

-- Apps difficulty: interview
-- Assurance level: unguarded