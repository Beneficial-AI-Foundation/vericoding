There is a directed graph with N vertices and N edges. The vertices are numbered 1, 2, ..., N.
The graph has the following N edges: (p_1, 1), (p_2, 2), ..., (p_N, N), and the graph is weakly connected. Here, an edge from Vertex u to Vertex v is denoted by (u, v), and a weakly connected graph is a graph which would be connected if each edge was bidirectional.
We would like to assign a value to each of the vertices in this graph so that the following conditions are satisfied. Here, a_i is the value assigned to Vertex i.
 - Each a_i is a non-negative integer.
 - For each edge (i, j), a_i \neq a_j holds.
 - For each i and each integer x(0 ≤ x < a_i), there exists a vertex j such that the edge (i, j) exists and x = a_j holds.
Determine whether there exists such an assignment.

-----Constraints-----
 - 2 ≤ N ≤ 200 000
 - 1 ≤ p_i ≤ N
 - p_i \neq i
 - The graph is weakly connected.

-----Input-----
Input is given from Standard Input in the following format:
N
p_1 p_2 ... p_N

-----Output-----
If the assignment is possible, print POSSIBLE; otherwise, print IMPOSSIBLE.

-----Sample Input-----
4
2 3 4 1

-----Sample Output-----
POSSIBLE

The assignment is possible: {a_i} = {0, 1, 0, 1} or {a_i} = {1, 0, 1, 0}.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
