You are participating in a contest which has $11$ problems (numbered $1$ through $11$). The first eight problems (i.e. problems $1, 2, \ldots, 8$) are scorable, while the last three problems ($9$, $10$ and $11$) are non-scorable ― this means that any submissions you make on any of these problems do not affect your total score.
Your total score is the sum of your best scores for all scorable problems. That is, for each scorable problem, you look at the scores of all submissions you made on that problem and take the maximum of these scores (or $0$ if you didn't make any submissions on that problem); the total score is the sum of the maximum scores you took.
You know the results of all submissions you made. Calculate your total score.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$ denoting the number of submissions you made.
- $N$ lines follow. For each $i$ ($1 \le i \le N$), the $i$-th of these lines contains two space-separated integers $p_i$ and $s_i$, denoting that your $i$-th submission was on problem $p_i$ and it received a score $s_i$.

-----Output-----
For each test case, print a single line containing one integer ― your total score.

-----Constraints-----
- $1 \le T \le 10$
- $1 \le N \le 1,000$
- $1 \le p_i \le 11$ for each valid $i$
- $0 \le s_i \le 100$ for each valid $i$

-----Subtasks-----
Subtask #1 (15 points): all submissions are on the same problem, i.e. $p_1 = p_2 = \ldots = p_N$
Subtask #2 (15 points): there is at most one submission made on each problem, i.e. $p_i \neq p_j$ for each valid $i, j$ ($i \neq j$)
Subtask #3 (70 points): original constraints

-----Example Input-----
2
5
2 45
9 100
8 0
2 15
8 90
1
11 1

-----Example Output-----
135
0

-----Explanation-----
Example case 1: The scorable problems with at least one submission are problems $2$ and $8$. For problem $2$, there are two submissions and the maximum score among them is $45$. For problem $8$, there are also two submissions and the maximum score is $90$. Hence, the total score is $45 + 90 = 135$.
Example case 2: No scorable problem is attempted, so the total score is $0$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded