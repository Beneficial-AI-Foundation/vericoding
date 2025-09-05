During quarantine chef’s friend invented a game. In this game there are two players, player 1 and Player 2. In center of garden there is one finish circle and both players are at different distances respectively $X$ and $Y$ from finish circle.
Between finish circle and Player 1 there are $X$ number of circles and between finish circle and Player 2 there are $Y$ number of circles. Both player wants to reach finish circle with minimum number of jumps. Player can jump one circle to another circle.
Both players can skip $2^0-1$ or $2^1- 1$ or …. or $2^N-1$ circles per jump. A player cannot skip same number of circles in a match more than once. If both players uses optimal way to reach finish circle what will be the difference of minimum jumps needed to reach finish circle by both players. 
If both players reach finish circle with same number of jumps answer will be $0$ $0$.

-----Input:-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The 
description of $T$ test cases follows.
- The first line of each test case contains 2 space separated integers $X$ and $Y$.

-----Output:-----
For each test case, print a single line containing 2 space-separated integers which player win and what is the difference between number of minimum jump required by both players to reach finish circle.

-----Constraints-----
- $1 \leq T \leq 10^5$
- $1 \leq X,Y \leq 2*10^7$

-----Sample Input:-----
2
4 5
3 5

-----Sample Output:-----
0 0
1 1

-----Explanation:-----
Test Case 1:

Test Case 2:

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible