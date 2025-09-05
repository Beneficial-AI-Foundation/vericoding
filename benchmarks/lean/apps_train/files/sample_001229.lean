Given an integer $x$, find two non-negative integers $a$ and $b$ such that $(a \wedge b) + (a \vee b) = x$, where $\wedge$ is the bitwise AND operation and $\vee$ is the bitwise OR operation.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains a single integer $x$.

-----Output-----
If there is no valid pair $(a, b)$, print a single line containing the integer $-1$. Otherwise, print a single line containing two space-separated integers $a$ and $b$.
If there are multiple solutions, you may print any one of them.

-----Constraints-----
- $1 \le T \le 10^5$
- $1 \le x \le 10^{18}$

-----Subtasks-----
Subtask #1 (30 points):
- $1 \le T \le 200$
- $1 \le x \le 200$
Subtask #2 (70 points): original constraints

-----Example Input-----
2
1
8

-----Example Output-----
0 1
5 3

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible