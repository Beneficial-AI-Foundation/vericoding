You are given three non-negative integers $X$, $Y$ and $N$. Find the number of integers $Z$ such that $0 \le Z \le N$ and $(X \oplus Z) < (Y \oplus Z)$, where $\oplus$ denotes the bitwise XOR operation.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains three space-separated integers $X$, $Y$ and $N$.

-----Output-----
For each test case, print a single line containing one integer ― the number of integers $Z$ which satisfy all conditions.

-----Constraints-----
- $1 \le T \le 1,000$
- $0 \le X, Y, N \le 2^{30} - 1$

-----Subtasks-----
Subtask #1 (5 points): $X, Y, N \le 2^6 - 1$
Subtask #2 (95 points): original constraints

-----Example Input-----
3
1 2 10
2 1 10
0 0 7

-----Example Output-----
6
5
0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible