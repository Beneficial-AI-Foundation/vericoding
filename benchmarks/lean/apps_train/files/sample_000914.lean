You are given two positive integers $A$ and $B$. Find the number of pairs of positive integers $(X, Y)$ such that $1 \le X \le A$, $1 \le Y \le B$ and $X + Y$ is even.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains two space-separated integers $A$ and $B$.

-----Output-----
For each test case, print a single line containing one integer ― the number of valid pairs.

-----Constraints-----
- $1 \le T \le 1,000$
- $1 \le A, B \le 10^9$

-----Subtasks-----
Subtask #1 (10 points): $A, B \le 10$
Subtask #2 (10 points): $A, B \le 1,000$
Subtask #3 (80 points): original constraints

-----Example Input-----
4
1 1
2 3
4 6
8 9

-----Example Output-----
1
3
12
36

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible