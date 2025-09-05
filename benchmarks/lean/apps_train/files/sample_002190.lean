You are given a sequence D_1, D_2, ..., D_N of length N.
The values of D_i are all distinct.
Does a tree with N vertices that satisfies the following conditions exist?
 - The vertices are numbered 1,2,..., N.
 - The edges are numbered 1,2,..., N-1, and Edge i connects Vertex u_i and v_i.
 - For each vertex i, the sum of the distances from i to the other vertices is D_i, assuming that the length of each edge is 1.
If such a tree exists, construct one such tree.

-----Constraints-----
 - 2 \leq N \leq 100000
 - 1 \leq D_i \leq 10^{12}
 - D_i are all distinct.

-----Input-----
Input is given from Standard Input in the following format:
N
D_1
D_2
:
D_N

-----Output-----
If a tree with n vertices that satisfies the conditions does not exist, print -1.
If a tree with n vertices that satisfies the conditions exist, print n-1 lines.
The i-th line should contain u_i and v_i with a space in between.
If there are multiple trees that satisfy the conditions, any such tree will be accepted.

-----Sample Input-----
7
10
15
13
18
11
14
19

-----Sample Output-----
1 2
1 3
1 5
3 4
5 6
6 7

The tree shown below satisfies the conditions.

def checkTreeWithDistances (N : Nat) (distances : List Nat) : List (Nat × Nat) ⊕ Unit :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded