On her way to ChefLand, Marichka noticed $10^K$ road signs (numbered $0$ through $10^K - 1$). For each valid $i$, the sign with number $i$ had the integer $i$ written on one side and $10^K-i-1$ written on the other side.
Now, Marichka is wondering — how many road signs have exactly two distinct decimal digits written on them (on both sides in total)? Since this number may be large, compute it modulo $10^9+7$.
For example, if $K = 3$, the two integers written on the road sign $363$ are $363$ and $636$, and they contain two distinct digits $3$ and $6$, but on the road sign $362$, there are integers $362$ and $637$, which contain four distinct digits — $2$, $3$, $6$ and $7$. On the road sign $11$, there are integers $11$ and $988$, which contain three distinct digits — $1$, $9$ and $8$.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains a single integer $K$.

-----Output-----
For each test case, print a single line containing one integer — the number of road signs with exactly two digits, modulo $10^9+7$.

-----Constraints-----
- $1 \le T \le 10^5$
- $1 \le K \le 10^9$

-----Subtasks-----
Subtask #1 (20 points): $1 \le T, K \le 5$
Subtask #2 (80 points): original constraints

-----Example Input-----
1
1

-----Example Output-----
10

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
