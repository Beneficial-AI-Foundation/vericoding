There are n kangaroos with pockets. Each kangaroo has a size (integer number). A kangaroo can go into another kangaroo's pocket if and only if the size of kangaroo who hold the kangaroo is at least twice as large as the size of kangaroo who is held.

Each kangaroo can hold at most one kangaroo, and the kangaroo who is held by another kangaroo cannot hold any kangaroos.

The kangaroo who is held by another kangaroo cannot be visible from outside. Please, find a plan of holding kangaroos with the minimal number of kangaroos who is visible.

-----Input-----

The first line contains a single integer — n (1 ≤ n ≤ 5·10^5). Each of the next n lines contains an integer s_{i} — the size of the i-th kangaroo (1 ≤ s_{i} ≤ 10^5).

-----Output-----

Output a single integer — the optimal number of visible kangaroos.

-----Examples-----
Input
8
2
5
7
6
9
8
4
2

Output
5

Input
8
9
1
6
2
6
5
8
3

Output
5

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible
