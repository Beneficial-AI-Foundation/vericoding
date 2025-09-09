/-
After fixing the mercury leak, Kim has arrived in the planning room, where he finds a square map of a field, with $N$ rows and $N$ columns. Each cell in the field is either empty, or has a lookout tower on it. Using his notes, he immediately realises that this field is where the JSA will build their new base!
Kim knows that Soum is a fan of symmetric base design, and will only approve of a base to be built if it is square. Furthermore, Soum also requires that all the rows in the base, and all the columns in the base have exactly one tower square in them. 
This means that a base plan is valid if and only if:
- It is square in shape
- Every row in the base has exactly one lookout tower in it.
- Every column in the base has exactly one lookout tower in it.
Kim notices that all the rows and all the columns in the field have exactly one tower square in them, but he knows that some of them could have been built to throw him off! Can you help Kim find how many valid base plans are possible in this field? Two base plans are considered different if one contains a cell in the grid that the other does not.
Please refer to the samples for more details.

-----Input:-----
- The first line of input contains $T$, the number of testcases.
- The first line of each testcase contains a single integer, $N$, representing the side length of the field.
- The next $N$ lines of each testcase contain a string of length $N$, consisting of only 0 and 1. If position $j$ in string $i$ is 0, it means that this the field has no tower at $[i][j]$, and if it is 1, then this cell does have a tower at $[i][j]$.
It is guaranteed that every row in the input will have exactly one tower, and every column in the input will also have exactly one tower.

-----Output:-----
For each testcase, output a single integer $K$, representing the number of different base plans possible.

-----Subtasks-----
- For all subtasks, $N \leq 2500$ and $T \leq 10$. 
- In addition, the sum of $N$ in any testfile is at most $2500$.
Subtask 1 [28 points] : All the towers will be on the diagonal from the top-left to the bottom-right positions. Formally, all positions where $i = j$ have a tower. And no other position has a tower
Subtask 2 [39 points] : $N \leq 600$
Subtask 3 [33 points] : $N \leq 2500$

-----Sample Input:-----
2
2
10
01
4
1000
0010
0100
0001

-----Sample Output:-----
3
8

-----Explanation:-----

In the first testcase, there are three valid base plans: The entire 2x2 square, the 1x1 square which contains only the cell (1, 1) and the 1x1 square which contains only the cell (2, 2).

In the second testcase, 

There are eight valid base plans:
- The 4x4 square with top left corner at (1, 1)
- The 3x3 square with top left corner at (1, 1)
- The 3x3 square with top left corner at (2, 2)
- The 3x3 square with top left corner at (1, 1)
- The 2x2 square with top left corner at (2, 2)
- The 1x1 square which contains only the cell (1, 1)
- The 1x1 square which contains only the cell (2, 3)
- The 1x1 square which contains only the cell (3, 2)
- The 1x1 square which contains only the cell (4, 4)
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_base_plans (n : Nat) (grid : List String) : Nat :=
  sorry

theorem diagonal_case (n : Nat) :
  let diagonal := List.range n |>.map (fun i =>
    String.mk (List.range n |>.map (fun j => if i = j then '1' else '0')))
  solve_base_plans n diagonal = n * (n + 1) / 2 :=
  sorry

theorem empty_grid_one :
  solve_base_plans 1 ["1"] = 1 :=
  sorry

theorem empty_grid_zero :
  solve_base_plans 1 ["0"] = 0 :=
  sorry

theorem all_zeros (n : Nat) :
  let zeros := List.replicate n (String.mk (List.replicate n '0'))
  solve_base_plans n zeros = 0 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_base_plans 2 ["10", "01"]

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve_base_plans 4 ["1000", "0010", "0100", "0001"]

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve_base_plans 3 ["100", "010", "001"]

-- Apps difficulty: interview
-- Assurance level: unguarded