Given is an undirected connected graph with N vertices numbered 1 to N, and M edges numbered 1 to M.
The given graph may contain multi-edges but not self loops.
Each edge has an integer label between 1 and N (inclusive).
Edge i has a label c_i, and it connects Vertex u_i and v_i bidirectionally.
Snuke will write an integer between 1 and N (inclusive) on each vertex (multiple vertices may have the same integer written on them) and then keep only the edges satisfying the condition below, removing the other edges.
Condition: Let x and y be the integers written on the vertices that are the endpoints of the edge. Exactly one of x and y equals the label of the edge.
We call a way of writing integers on the vertices good if (and only if) the graph is still connected after removing the edges not satisfying the condition above. Determine whether a good way of writing integers exists, and present one such way if it exists.

-----Constraints-----
 - 2 \leq N \leq 10^5
 - N-1 \leq M \leq 2 \times 10^5
 - 1 \leq u_i,v_i,c_i \leq N
 - The given graph is connected and has no self-loops.

-----Input-----
Input is given from Standard Input in the following format:
N M
u_1 v_1 c_1
\vdots
u_M v_M c_M

-----Output-----
If there is no good way of writing integers, print No.
Otherwise, print N lines. The i-th line should contain the integer written on Vertex i.
Any good way of writing integers will be accepted.

-----Sample Input-----
3 4
1 2 1
2 3 2
3 1 3
1 3 1

-----Sample Output-----
1
2
1

 - We write 1, 2, and 1 on Vertex 1, 2, and 3, respectively.
 - Edge 1 connects Vertex 1 and 2, and its label is 1.
 - Only the integer written on Vertex 1 equals the label, so this edge will not get removed.
 - Edge 2 connects Vertex 2 and 3, and its label is 2.
 - Only the integer written on Vertex 2 equals the label, so this edge will not be removed.
 - Edge 3 connects Vertex 1 and 3, and its label is 3.
 - Both integers written on the vertices differ from the label, so this edge will be removed.
 - Edge 4 connects Vertex 1 and 3, and its label is 1.
 - Both integers written on the vertices equal the label, so this edge will be removed.
 - After Edge 3 and 4 are removed, the graph will still be connected, so this is a good way of writing integers.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded