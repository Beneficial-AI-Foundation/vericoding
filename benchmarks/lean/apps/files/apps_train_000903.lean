/-
You are given a tree with $N$ vertices (numbered $1$ through $N$) and a bag with $N$ markers. There is an integer written on each marker; each of these integers is $0$, $1$ or $2$. You must assign exactly one marker to each vertex.
Let's define the unattractiveness of the resulting tree as the maximum absolute difference of integers written on the markers in any two vertices which are connected by an edge.
Find the minimum possible unattractiveness of the resulting tree.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers denoting the numbers on markers in the bag.
- Each of the next $N-1$ lines contains two space-separated integers $u$ and $v$ denoting an edge between vertices $u$ and $v$.

-----Output-----
For each test case, print a single line containing one integer — the minimum unattractiveness.

-----Constraints-----
- $1 \le T \le 30$
- $1 \le N \le 100$
- $1 \le u, v \le N$
- the graph described on the input is a tree

-----Example Input-----
3
3
0 1 1
1 2
1 3
3
0 1 2
1 2
1 3
4
2 2 2 2
1 2
1 3
3 4

-----Example Output-----
1
1
0

-----Explanation-----
Example case 1:
-/

-- <vc-helpers>
-- </vc-helpers>

def min_unattractiveness (n : Nat) (markers : List Nat) (edges : List (List Nat)) : Nat :=
sorry

theorem min_unattractiveness_same_marker (marker : Nat) : 
  min_unattractiveness 2 [marker, marker] [[1,2]] = 0 := by
  sorry

theorem min_unattractiveness_different_markers :
  min_unattractiveness 2 [0,2] [[1,2]] = 2 := by
  sorry

theorem min_unattractiveness_simple_tree :
  min_unattractiveness 3 [0,1,1] [[1,2], [1,3]] = 1 := by
  sorry

theorem min_unattractiveness_three_markers :
  min_unattractiveness 3 [0,1,2] [[1,2], [1,3]] = 1 := by
  sorry

theorem min_unattractiveness_all_same :
  min_unattractiveness 4 [2,2,2,2] [[1,2], [1,3], [3,4]] = 0 := by
  sorry

theorem min_unattractiveness_all_ones {n : Nat} (h : n > 0) : 
  min_unattractiveness n (List.replicate n 1) (List.range (n-1) |>.map (λ i => [i+1, i+2])) = 0 := by
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_unattractiveness 3 [0, 1, 1] [[1, 2], [1, 3]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_unattractiveness 3 [0, 1, 2] [[1, 2], [1, 3]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_unattractiveness 4 [2, 2, 2, 2] [[1, 2], [1, 3], [3, 4]]

-- Apps difficulty: interview
-- Assurance level: unguarded