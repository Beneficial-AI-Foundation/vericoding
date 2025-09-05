You are given two integers $N$ and $M$. Find the number of sequences $A_1, A_2, \ldots, A_N$, where each element is an integer between $1$ and $M$ (inclusive) and no three consecutive elements are equal. Since this number could be very large, compute it modulo $10^9+7$.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains two space-separated integers $N$ and $M$.

-----Output-----
For each test case, print a single line containing one integer ― the number of valid sequences modulo $10^9+7$.

-----Constraints-----
- $1 \le T \le 10^5$
- $1 \le N, M \le 10^{18}$

-----Subtasks-----
Subtask #1 (50 points):
- $T \le 20$
- $N \le 10^5$
Subtask #2 (50 points): original constraints

-----Example Input-----
2 
2 2
3 4

-----Example Output-----
4
60

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible