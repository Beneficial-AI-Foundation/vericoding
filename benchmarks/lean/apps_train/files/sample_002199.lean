Snuke has a rooted tree with N+1 vertices.
The vertices are numbered 0 through N, and Vertex 0 is the root of the tree.
The parent of Vertex i (1 \leq i \leq N) is Vertex p_i.
Besides this tree, Snuke also has an box which is initially empty and many marbles, and playing with them.
The play begins with placing one marble on some of the vertices, then proceeds as follows:
 - If there is a marble on Vertex 0, move the marble into the box.
 - Move each marble from the vertex to its parent (all at once).
 - For each vertex occupied by two or more marbles, remove all the marbles from the vertex.
 - If there exists a vertex with some marbles, go to Step 1. Otherwise, end the play.
There are 2^{N+1} ways to place marbles on some of the vertices.
For each of them, find the number of marbles that will be in the box at the end of the play, and compute the sum of all those numbers modulo 1,000,000,007.

-----Constraints-----
 - 1 \leq N < 2 \times 10^{5}
 - 0 \leq p_i < i

-----Partial Scores-----
 - In the test set worth 400 points, N < 2{,}000.

-----Input-----
Input is given from Standard Input in the following format:
N
p_1 p_2 ... p_{N}

-----Output-----
Print the answer.

-----Sample Input-----
2
0 0

-----Sample Output-----
8

When we place a marble on both Vertex 1 and 2, there will be multiple marbles on Vertex 0 by step 2. In such a case, these marbles will be removed instead of being moved to the box.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded