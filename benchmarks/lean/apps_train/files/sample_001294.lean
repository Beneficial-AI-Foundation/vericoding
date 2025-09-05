You are given a sequence $A_1, A_2, \ldots, A_N$. You should select a (not necessarily contiguous) subsequence of $A$ and reverse it. In other words, if you select a subsequence $A_{i_1}, A_{i_2}, \ldots, A_{i_K}$ ($1 \le i_1 < \ldots < i_K \le N$), then for each valid $j$, the $i_j$-th element of the resulting sequence is equal to the $i_{K+1-j}$-th element of the original sequence; all other elements are the same as in the original sequence.
In the resulting sequence, you want to calculate the maximum sum of a contiguous subsequence (possibly an empty sequence, with sum $0$). Find its maximum possible value and a subsequence which you should select in order to obtain this maximum value. If there are multiple solutions, you may find any one of them.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
For each test case, print two lines.
- The first of these lines should contain a single integer ― the maximum possible sum of a contiguous subsequence.
- The second line should contain an integer $K$ followed by a space and $K$ space-separated integers $i_1, i_2, \ldots, i_K$.

-----Constraints-----
- $1 \le T \le 2,000$
- $2 \le N \le 10^5$
- $|A_i| \le 10^9$ for each valid $i$
- the sum of $N$ over all test cases does not exceed $2 \cdot 10^6$

-----Example Input-----
2
5
-4 2 -4 3 -5
3
-3 -2 -1

-----Example Output-----
5
2 2 3
0
0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded