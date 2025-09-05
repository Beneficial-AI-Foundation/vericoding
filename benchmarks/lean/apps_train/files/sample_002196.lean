There is a simple undirected graph with N vertices and M edges.
The vertices are numbered 1 through N, and the edges are numbered 1 through M.
Edge i connects Vertex U_i and V_i.
Also, Vertex i has two predetermined integers A_i and B_i.
You will play the following game on this graph.
First, choose one vertex and stand on it, with W yen (the currency of Japan) in your pocket.
Here, A_s \leq W must hold, where s is the vertex you choose.
Then, perform the following two kinds of operations any number of times in any order:
 - Choose one vertex v that is directly connected by an edge to the vertex you are standing on, and move to vertex v. Here, you need to have at least A_v yen in your pocket when you perform this move.
 - Donate B_v yen to the vertex v you are standing on. Here, the amount of money in your pocket must not become less than 0 yen.
You win the game when you donate once to every vertex.
Find the smallest initial amount of money W that enables you to win the game.

-----Constraints-----
 - 1 \leq N \leq 10^5
 - N-1 \leq M \leq 10^5
 - 1 \leq A_i,B_i \leq 10^9
 - 1 \leq U_i < V_i \leq N
 - The given graph is connected and simple (there is at most one edge between any pair of vertices).

-----Input-----
Input is given from Standard Input in the following format:
N M
A_1 B_1
A_2 B_2
:
A_N B_N
U_1 V_1
U_2 V_2
:
U_M V_M

-----Output-----
Print the smallest initial amount of money W that enables you to win the game.

-----Sample Input-----
4 5
3 1
1 2
4 1
6 2
1 2
2 3
2 4
1 4
3 4

-----Sample Output-----
6

If you have 6 yen initially, you can win the game as follows:
 - Stand on Vertex 4. This is possible since you have not less than 6 yen.
 - Donate 2 yen to Vertex 4. Now you have 4 yen.
 - Move to Vertex 3. This is possible since you have not less than 4 yen.
 - Donate 1 yen to Vertex 3. Now you have 3 yen.
 - Move to Vertex 2. This is possible since you have not less than 1 yen.
 - Move to Vertex 1. This is possible since you have not less than 3 yen.
 - Donate 1 yen to Vertex 1. Now you have 2 yen.
 - Move to Vertex 2. This is possible since you have not less than 1 yen.
 - Donate 2 yen to Vertex 2. Now you have 0 yen.
If you have less than 6 yen initially, you cannot win the game. Thus, the answer is 6.

def DSU.merge (dsu : DSU n) (a b : Nat) : Nat := sorry
def DSU.leader (dsu : DSU n) (a : Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible
