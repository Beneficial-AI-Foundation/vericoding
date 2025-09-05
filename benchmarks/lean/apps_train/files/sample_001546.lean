You are at the top left cell $(1, 1)$ of an $n \times m$ labyrinth. Your goal is to get to the bottom right cell $(n, m)$. You can only move right or down, one cell per step. Moving right from a cell $(x, y)$ takes you to the cell $(x, y + 1)$, while moving down takes you to the cell $(x + 1, y)$.

Some cells of the labyrinth contain rocks. When you move to a cell with rock, the rock is pushed to the next cell in the direction you're moving. If the next cell contains a rock, it gets pushed further, and so on.

The labyrinth is surrounded by impenetrable walls, thus any move that would put you or any rock outside of the labyrinth is illegal.

Count the number of different legal paths you can take from the start to the goal modulo $10^9 + 7$. Two paths are considered different if there is at least one cell that is visited in one path, but not visited in the other.

-----Input-----

The first line contains two integers $n, m$ — dimensions of the labyrinth ($1 \leq n, m \leq 2000$).

Next $n$ lines describe the labyrinth. Each of these lines contains $m$ characters. The $j$-th character of the $i$-th of these lines is equal to "R" if the cell $(i, j)$ contains a rock, or "." if the cell $(i, j)$ is empty.

It is guaranteed that the starting cell $(1, 1)$ is empty.

-----Output-----

Print a single integer — the number of different legal paths from $(1, 1)$ to $(n, m)$ modulo $10^9 + 7$.

-----Examples-----
Input
1 1
.

Output
1

Input
2 3
...
..R

Output
0

Input
4 4
...R
.RR.
.RR.
R...

Output
4

-----Note-----

In the first sample case we can't (and don't have to) move, hence the only path consists of a single cell $(1, 1)$.

In the second sample case the goal is blocked and is unreachable.

Illustrations for the third sample case can be found here: https://assets.codeforces.com/rounds/1225/index.html

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
