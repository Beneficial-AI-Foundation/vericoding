You are given a weighted undirected graph consisting of n$n$ nodes and m$m$ edges. The nodes are numbered from 1$1$ to n$n$. The graph does not contain any multiple edges or self loops.
A walk W$W$ on the graph is a sequence of vertices (with repetitions of vertices and edges allowed) such that every adjacent pair of vertices in the sequence is an edge of the graph. We define the cost of a walk W$W$, Cost(W)$Cost(W)$, as the maximum over the weights of the edges along the walk. 
You will be given q$q$ queries. In each query, you will be given an integer X$X$.

You have to count the number of different walks W$W$ of length 4$4$ such that Cost(W)$Cost(W)$ = X$X$.

Two walks are considered different if they do not represent the same edge sequence.

-----Input:-----
- First line contains 2 integers : the number of nodes n$n$ and number of edges m$m$.
- Next m$m$ lines each describe u$u$, v$v$ and w$w$, describing an edge between u$u$ and v$v$ with weight w$w$.
- Next line contains q$q$, the number of queries.
- Next q$q$ lines each describe an integer X$X$ - the cost of the walk in the query.

-----Output:-----
For each query, output in a single line the number of different possible walks.

-----Constraints-----
- 1≤n≤100$1 \leq n \leq 100$
- 1≤m≤n(n−1)2$1 \leq m \leq \frac{n (n-1)}{2}$
- 1≤u,v≤n$1 \leq u, v \leq n$
- 1≤w≤100$1 \leq w \leq 100$
- 1≤q≤100$1 \leq q \leq 100$
- 1≤X≤100$1 \leq X \leq 100$

-----Sample Input:-----
3 3
1 2 1
2 3 2
3 1 3
3
1
2
3

-----Sample Output:-----
2
10
36

-----EXPLANATION:-----
For X=2$X = 2$, all possible 10$10$ walks are listed below :
- 1 -> 2 -> 1 -> 2 -> 3
- 1 -> 2 -> 3 -> 2 -> 1
- 1 -> 2 -> 3 -> 2 -> 3
- 2 -> 1 -> 2 -> 3 -> 2
- 2 -> 3 -> 2 -> 1 -> 2
- 2 -> 3 -> 2 -> 3 -> 2
- 3 -> 2 -> 1 -> 2 -> 1
- 3 -> 2 -> 1 -> 2 -> 3
- 3 -> 2 -> 3 -> 2 -> 1
- 3 -> 2 -> 3 -> 2 -> 3

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
