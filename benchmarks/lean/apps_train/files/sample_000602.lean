In a regular table tennis match, the player who serves changes every time after 2 points are scored, regardless of which players scored them.
Chef and Cook are playing a different match — they decided that the player who serves would change every time after $K$ points are scored instead (again regardless of which players scored them). When the game starts, it's Chef's turn to serve.
You are given the current number of points scored by Chef and Cook ($P_1$ and $P_2$ respectively). Find out whether Chef or Cook has to serve next.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains three space-separated integers $P_1$, $P_2$ and $K$.

-----Output-----
For each test case, print a single line containing the string "CHEF" if it is Chef's turn or "COOK" if it is Cook's turn.

-----Constraints-----
- $1 \le T \le 10^5$
- $1 \le K \le 10^{9}$
- $0 \le P_1, P_2 \le 10^{9}$ 

-----Subtasks-----
Subtask #1 (100 points): original constraints

-----Example Input-----
3
1 3 2
0 3 2
34 55 2

-----Example Output-----
CHEF
COOK
CHEF

-----Explanation-----
Example case 1: Chef serves for the first two points, Cook serves for the next two, so Chef has to serve again now.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded