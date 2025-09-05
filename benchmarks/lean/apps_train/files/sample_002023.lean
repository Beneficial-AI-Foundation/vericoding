DZY loves Physics, and he enjoys calculating density.

Almost everything has density, even a graph. We define the density of a non-directed graph (nodes and edges of the graph have some values) as follows: $\left\{\begin{array}{ll}{\frac{v}{e}} & {(e > 0)} \\{0} & {(e = 0)} \end{array} \right.$ where v is the sum of the values of the nodes, e is the sum of the values of the edges.

Once DZY got a graph G, now he wants to find a connected induced subgraph G' of the graph, such that the density of G' is as large as possible.

An induced subgraph G'(V', E') of a graph G(V, E) is a graph that satisfies:  $V^{\prime} \subseteq V$;  edge $(a, b) \in E^{\prime}$ if and only if $a \in V^{\prime}, b \in V^{\prime}$, and edge $(a, b) \in E$;  the value of an edge in G' is the same as the value of the corresponding edge in G, so as the value of a node. 

Help DZY to find the induced subgraph with maximum density. Note that the induced subgraph you choose must be connected. [Image] 

-----Input-----

The first line contains two space-separated integers n (1 ≤ n ≤ 500), $m(0 \leq m \leq \frac{n(n - 1)}{2})$. Integer n represents the number of nodes of the graph G, m represents the number of edges.

The second line contains n space-separated integers x_{i} (1 ≤ x_{i} ≤ 10^6), where x_{i} represents the value of the i-th node. Consider the graph nodes are numbered from 1 to n.

Each of the next m lines contains three space-separated integers a_{i}, b_{i}, c_{i} (1 ≤ a_{i} < b_{i} ≤ n; 1 ≤ c_{i} ≤ 10^3), denoting an edge between node a_{i} and b_{i} with value c_{i}. The graph won't contain multiple edges.

-----Output-----

Output a real number denoting the answer, with an absolute or relative error of at most 10^{ - 9}.

-----Examples-----
Input
1 0
1

Output
0.000000000000000

Input
2 1
1 2
1 2 1

Output
3.000000000000000

Input
5 6
13 56 73 98 17
1 2 56
1 3 29
1 4 42
2 3 95
2 4 88
3 4 63

Output
2.965517241379311

-----Note-----

In the first sample, you can only choose an empty subgraph, or the subgraph containing only node 1.

In the second sample, choosing the whole graph is optimal.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded
