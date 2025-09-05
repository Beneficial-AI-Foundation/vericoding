You are given a sequence $A_1, A_2, \ldots, A_N$. Calculate the number of ways to remove a non-empty contiguous subsequence from it such that the resulting sequence is non-empty and strictly increasing.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
For each test case, print a single line containing one integer ― the number of ways.

-----Constraints-----
- $1 \le T \le 10$
- $1 \le N \le 10^5$
- $|A_i| \le 10^9$ for each valid $i$

-----Subtasks-----
Subtask #1 (40 points): $N \le 1,000$
Subtask #2 (60 points): original constraints

-----Example Input-----
2
3
1 1 2
4
2 4 3 5

-----Example Output-----
4
7

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
