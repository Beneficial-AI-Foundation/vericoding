There is a tree with N vertices numbered 1 through N.
The i-th edge connects Vertex x_i and y_i.
Each vertex is painted white or black.
The initial color of Vertex i is represented by a letter c_i.
c_i = W represents the vertex is white; c_i = B represents the vertex is black.
A cat will walk along this tree.
More specifically, she performs one of the following in one second repeatedly:
 - Choose a vertex that is adjacent to the vertex where she is currently, and move to that vertex. Then, invert the color of the destination vertex.
 - Invert the color of the vertex where she is currently.
The cat's objective is to paint all the vertices black. She may start and end performing actions at any vertex.
At least how many seconds does it takes for the cat to achieve her objective?

-----Constraints-----
 - 1 ≤ N ≤ 10^5
 - 1 ≤ x_i,y_i ≤ N (1 ≤ i ≤ N-1)
 - The given graph is a tree.
 - c_i = W or c_i = B.

-----Input-----
Input is given from Standard Input in the following format:
N
x_1 y_1
x_2 y_2
:
x_{N-1} y_{N-1}
c_1c_2..c_N

-----Output-----
Print the minimum number of seconds required to achieve the objective.

-----Sample Input-----
5
1 2
2 3
2 4
4 5
WBBWW

-----Sample Output-----
5

The objective can be achieved in five seconds, for example, as follows:
 - Start at Vertex 1. Change the color of Vertex 1 to black.
 - Move to Vertex 2, then change the color of Vertex 2 to white.
 - Change the color of Vertex 2 to black.
 - Move to Vertex 4, then change the color of Vertex 4 to black.
 - Move to Vertex 5, then change the color of Vertex 5 to black.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
