Fennec and Snuke are playing a board game.
On the board, there are N cells numbered 1 through N, and N-1 roads, each connecting two cells. Cell a_i is adjacent to Cell b_i through the i-th road. Every cell can be reached from every other cell by repeatedly traveling to an adjacent cell. In terms of graph theory, the graph formed by the cells and the roads is a tree.
Initially, Cell 1 is painted black, and Cell N is painted white. The other cells are not yet colored.
Fennec (who goes first) and Snuke (who goes second) alternately paint an uncolored cell.
More specifically, each player performs the following action in her/his turn:
 - Fennec: selects an uncolored cell that is adjacent to a black cell, and paints it black.
 - Snuke: selects an uncolored cell that is adjacent to a white cell, and paints it white.
A player loses when she/he cannot paint a cell. Determine the winner of the game when Fennec and Snuke play optimally.

-----Constraints-----
 - 2 \leq N \leq 10^5
 - 1 \leq a_i, b_i \leq N
 - The given graph is a tree.

-----Input-----
Input is given from Standard Input in the following format:
N
a_1 b_1
:
a_{N-1} b_{N-1}

-----Output-----
If Fennec wins, print Fennec; if Snuke wins, print Snuke.

-----Sample Input-----
7
3 6
1 2
3 1
7 4
5 7
1 4

-----Sample Output-----
Fennec

For example, if Fennec first paints Cell 2 black, she will win regardless of Snuke's moves.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
