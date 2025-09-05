In a cricket game, an over is a set of six valid deliveries of balls performed by one player ― the bowler for this over.
Consider a cricket game with a series of $N$ overs (numbered $1$ through $N$) played by $K$ players (numbered $1$ through $K$). Each player may be the bowler for at most $L$ overs in total, but the same player may not be the bowler for any two consecutive overs. Assign exactly one bowler to each over in such a way that these rules are satisfied or determine that no such assignment exists.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains three space-separated integers $N$, $K$ and $L$. 

-----Output-----
For each test case:
- If there is no valid assignment of bowlers to overs, print a single line containing the integer $-1$.
- Otherwise, print a single line containing $N$ space-separated integers. For each valid $i$, the $i$-th of these integers should be the number of the player assigned as the bowler for the $i$-th over.

-----Constraints-----
- $1 \le T \le 30$
- $1 \le N, K, L \le 10,000$

-----Example Input-----
2
4 3 2
5 4 1

-----Example Output-----
1 2 3 2
-1

-----Explanation-----
Example case 1: The following is a valid assignment:
- Bowler 1 bowls the $1$-st over.
- Bowler 2 bowls the $2$-nd and $4$-th overs.
- Bowler 3 bowls the $3$-rd over.
It is valid since no bowler bowls more than $2$ overs and each two consecutive overs have different bowlers.
Example case 2: There is no valid assignment in which each of $4$ players bowls at most $1$ over out of $5$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded