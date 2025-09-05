Let's call some positive integer classy if its decimal representation contains no more than $3$ non-zero digits. For example, numbers $4$, $200000$, $10203$ are classy and numbers $4231$, $102306$, $7277420000$ are not.

You are given a segment $[L; R]$. Count the number of classy integers $x$ such that $L \le x \le R$.

Each testcase contains several segments, for each of them you are required to solve the problem separately.

-----Input-----

The first line contains a single integer $T$ ($1 \le T \le 10^4$) — the number of segments in a testcase.

Each of the next $T$ lines contains two integers $L_i$ and $R_i$ ($1 \le L_i \le R_i \le 10^{18}$).

-----Output-----

Print $T$ lines — the $i$-th line should contain the number of classy integers on a segment $[L_i; R_i]$.

-----Example-----
Input
4
1 1000
1024 1024
65536 65536
999999 1000001

Output
1000
1
0
2

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded