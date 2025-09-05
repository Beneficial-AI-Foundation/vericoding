Vasya's older brother, Petya, attends an algorithm course in his school. Today he learned about matchings in graphs. Formally, a set of edges in a graph is called a matching if no pair of distinct edges in the set shares a common endpoint.
Petya instantly came up with an inverse concept, an antimatching. In an antimatching, any pair of distinct edges should have a common endpoint.
Petya knows that finding a largest matching in a graph is a somewhat formidable task. He wonders if finding the largest antimatching is any easier. Help him find the number of edges in a largest antimatching in a given graph.

-----Input:-----
The first line contains T$T$, number of test cases per file.
The first line of each test case contains two integers n$n$ and m−$m-$ the number of vertices and edges of the graph respectively (1≤n≤104$1 \leq n \leq 10^4$, 0≤m≤104$0 \leq m \leq 10^4$).
The next m$m$ lines describe the edges. The i$i$-th of these lines contains two integers ui$u_i$ and vi−$v_i-$ the indices of endpoints of the i$i$-th edge (1≤ui,vi≤n$1 \leq u_i, v_i \leq n$, ui≠vi$u_i \neq v_i$).
It is guaranteed that the graph does not contain self-loops nor multiple edges. It is not guaranteed that the graph is connected.

-----Output:-----
Print a single number per test case −$-$ the maximum size of an antichain in the graph.

-----Constraints-----
- 1≤T≤10$1 \leq T \leq 10$
- 1≤n≤104$1 \leq n \leq 10^4$
- 0≤m≤104$0 \leq m \leq 10^4$
- 1≤ui,vi≤n$1 \leq u_i, v_i \leq n$
- ui≠vi$u_i \neq v_i$

-----Sample Input:-----
3
3 3
1 2
1 3
2 3
4 2
1 2
3 4
5 0

-----Sample Output:-----
3
1
0

-----EXPLANATION:-----
In the first sample all three edges form an antimatching.
In the second sample at most one of the two edges can be included in an antimatching since they do not share common endpoints.
In the third sample there are no edges, hence the answer is 0$0$.

def solve_antimatching (n m : Nat) (edges : List (Nat × Nat)) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
