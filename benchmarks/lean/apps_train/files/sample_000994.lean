You are given a tree rooted at node $1$ with $N$ vertices. The $i$$th$ vertex initially has value $A_i (1 \leq i \leq N)$. You are also given $Q$ queries. 
In each query you are given a vertex $V$.  Let $S = \{ S_1 , S_2 , ... S_x \} $ denote the set of vertices such that $S_i$ is in the subtree of $V$, distance between $S_i$ and $V$ is even and $S_i \neq V$ for all $i$. For all $S_i$ , add $A$$S_i$ to $A_V$ and change the value of $A$$S_i$ to zero.
Find the values of all the vertices after all queries are performed. 
Note-The distance between two vertices is defined as the number of edges
traversed on the shortest path from one vertex to the other.

-----Input:-----
- The first line contains an integer $T$ denoting the number of test cases.
- The first line of each test case contain two integers $N$ and $Q$.
- The second line contains $N$ space separated integers, $A_1, A_2, ..., A_n$ denoting the initial values of the vertices.
- The next $N-1$ lines contain two integers $u$ and $v$ denoting an edge between $u$and $v$.
- The next $Q$ lines contain a single integer which is the query.

-----Output:-----
- Print a single line containing $N$ integers for each test case which is the final values of the vertices.

-----Constraints:-----
- $1\leq T \leq 10$
- $1 \leq N \leq 200000$
- $1 \leq Q \leq 200000$
- $0 \leq A_i \leq 10^9$
- The sum of $N$ over all test cases does not exceed $200000$.
- The sum of $Q$ over all test cases does not exceed $200000$.

-----Sample Input-----
1
4 3
6 2 7 3
1 2
2 3
3 4
3
2
1

-----Sample Output-----
13 5 0 0

-----Explanation-----
Node $3$ has no child in its subtree which is at  an even distance so there is no change in the values. Values of nodes after $1st$ query: $6, 2, 7, 3$.
Node $4$ is at an even distance in the subtree of node $2$ so $A_4$ gets added to $A_2$ and $A_4$ becomes 0. Values of nodes after $2nd$ query: $6, 5, 7, 0$.
Node $3$ is at an even distance in the subtree of node $1$ so $A_3$ gets added to $A_1$ and $A_3$ becomes 0. Values of nodes after $3rd$ query: $13, 5, 0, 0$.

def find_sequence (arr : List Nat) : List Nat := sorry

theorem find_sequence_non_negative (arr : List Nat) : 
  ∀ x ∈ find_sequence arr, x ≥ 0 := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded