You are given a sequence $A_1, A_2, \ldots, A_N$. For each $k$ ($1 \le k \le N$), let's define a function $f(k)$ in the following way:
- Consider a sequence $B_1, B_2, \ldots, B_N$, which is created by setting $A_k = 0$. Formally, $B_k = 0$ and $B_i = A_i$ for each valid $i \neq k$.
- $f(k)$ is the number of ways to split the sequence $B$ into two non-empty contiguous subsequences with equal sums.
Find the sum $S = f(1) + f(2) + \ldots + f(N)$.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
For each test case, print a single line containing one integer — the sum $S$.

-----Constraints-----
- $1 \le T \le 10$
- $2 \le N \le 2 \cdot 10^5$
- $1 \le |A_i| \le 10^9$ for each valid $i$

-----Example Input-----
2
6
1 2 1 1 3 1
3
4 1 4

-----Example Output-----
6
2

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
