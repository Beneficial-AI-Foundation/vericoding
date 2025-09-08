/-
The garden has a tree with too many leaves on it and gardner wants to cut the unwanted leaves. This is a rooted tree, where a node $v$ is called parent of another node $u$, if there exists a directed edge from $v$ to $u$. Leaf node is a node with no outgoing edges.
Gardner cuts the tree in a peculiar way:
- For each parent node(which has a valid leaf node attached to it), he cuts $x$ leaf nodes, such that $x$ is a multiple of 3.
Example : If a parent node has 7 leaf nodes, 6 leaf nodes will be cut and 1 will be left.
- If a parent has all its leaf nodes cut, only then the parent node itself becomes a new leaf node. If new leaf nodes are created, Gardner repeats step 1 until he can cut no more leaf nodes.
After completing all operations, gardner wants to know the minimum number of nodes left on the tree.

It is guaranteed that the given input is a rooted tree.
The root of the tree is vertex 1.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- First line of each testcase contains an integer $n$, the number of vertices in the tree. 
- Second line of each testcase contains array $A$ of size $n-1$, where $A_{i}(1≤i≤n-1)$, is the index of the parent of the $(i+1)^{th}$ vertex. 

-----Output:-----
For each testcase, output single integer, the number of nodes finally left on the tree.  

-----Constraints-----
- $1 \leq T \leq 10$
- $2 \leq n \leq 10^5$ 
- $1 \leq A_i \leq i$

-----Sample Input:-----
1

13

1 1 1 1 1 4 3 4 4 3 4 3 

-----Sample Output:-----
4

-----EXPLANATION:-----
-/

def solve_tree_trimming (n : Nat) (parents : List Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def is_valid_tree (n : Nat) (parents : List Nat) : Bool :=
  sorry

theorem tree_trimming_bounds {n : Nat} {parents : List Nat} 
  (h1 : n ≥ 2) (h2 : is_valid_tree n parents = true) :
  let result := solve_tree_trimming n parents
  1 ≤ result ∧ result ≤ n :=
sorry

theorem small_tree_optimum {n : Nat} {parents : List Nat}
  (h1 : n ≥ 2) (h2 : n ≤ 3) (h3 : is_valid_tree n parents = true) :
  solve_tree_trimming n parents = n :=
sorry

theorem line_tree_bounds {n : Nat} 
  (h : n ≥ 2) :
  let parents := List.range (n-1)
  let result := solve_tree_trimming n parents
  1 ≤ result ∧ result ≤ n :=
sorry

theorem star_tree_bounds {n : Nat}
  (h : n ≥ 2) :
  let parents := List.replicate (n-1) 1
  let result := solve_tree_trimming n parents  
  1 ≤ result ∧ result ≤ n :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_tree_trimming 13 [1, 1, 1, 1, 1, 4, 3, 4, 4, 3, 4, 3]

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_tree_trimming 3 [1, 1]

-- Apps difficulty: interview
-- Assurance level: unguarded