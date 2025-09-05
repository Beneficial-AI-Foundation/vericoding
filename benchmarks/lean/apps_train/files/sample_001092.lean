Chef’s girlfriend is angry with him because he forgot her birthday. Chef decided to please her by gifting her a Love Graph. 
Chef has $N$ vertices: $V_1, V_2, \dots, V_N$. Love Graph is an undirected multigraph with no self-loops and can be constructed by performing the following operations:-
- Choose an integer $i$ ($1 \leq i \leq N$)
- Choose another integer $j \space \space \{ (i \neq j) \text{ and } (1 \leq j \leq N) \}$
- Make an edge between $V_i$ and $V_j$
- Set $i = j$
- Repeat steps $2, 3$ and $4$ in order $M-1$ more times.
Find the number of ways in which Chef can construct a Love Graph. Since the answer can be very large, compute it modulo $10^9+7$.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows. 
- The first line of each test case contains two space-separated integers $N$ and $M$.

-----Output-----
For each test case, print a single line containing one integer — the number of ways in which Chef can construct a Love Graph modulo $10^9+7$.

-----Constraints-----
- $1 \leq T \leq 10^5$
- $2 \leq N \leq 10^9$
- $1 \leq M \leq 10^{18}$

-----Subtasks-----
- 30 points:
- $1 \leq T \leq 100$
- $2 \leq N \leq 10$
- $1 \leq M \leq 10$ 
- 70 points: original constraints

-----Sample Input-----
1

2 1   

-----Sample Output-----
2   

-----Explanation-----
There are two ways of constructing Love Graph.

In first way, we pick Vertex 1 and then join with Vertex 2.

In second way, we pick Vertex 2 and then join with Vertex 1.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
