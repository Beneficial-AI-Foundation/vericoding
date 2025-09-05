Let's define a periodic infinite sequence S$S$ (0$0$-indexed) with period K$K$ using the formula Si=(i%K)+1$S_i = (i \% K) + 1$.
Chef has found a sequence of positive integers A$A$ with length N$N$ buried underground. He suspects that it is a contiguous subsequence of some periodic sequence. Unfortunately, some elements of A$A$ are unreadable. Can you tell Chef the longest possible period K$K$ of an infinite periodic sequence which contains A$A$ (after suitably filling in the unreadable elements) as a contiguous subsequence?

-----Input-----
- The first line of the input contains a single integer T$T$ denoting the number of test cases. The description of T$T$ test cases follows.
- The first line of each test case contains a single integer N$N$. 
- The second line contains N$N$ space-separated integers A1,A2,…,AN$A_1, A_2, \dots, A_N$. Unreadable elements are denoted by −1$-1$.

-----Output-----
For each test case, print a single line.
- If the period can be arbitrarily large, this line should contain a single string "inf".
- Otherwise, if A$A$ cannot be a contiguous subsequence of a periodic sequence, it should contain a single string "impossible".
- Otherwise, it should contain a single integer — the maximum possible period.

-----Constraints-----
- 1≤T≤100$1 \le T \le 100$
- 2≤N≤105$2 \le N \le 10^5$
- the sum of N$N$ over all test cases does not exceed 106$10^6$
- for each valid i$i$, 1≤Ai≤106$1 \le A_i \le 10^6$ or Ai=−1$A_i = -1$

-----Subtasks-----
Subtask #1 (50 points):
- 2≤N≤1,000$2 \le N \le 1,000$
- the sum of N$N$ over all test cases does not exceed 10,000$10,000$
Subtask #2 (50 points): original constraints

-----Example Input-----
3
3
-1 -1 -1
5
1 -1 -1 4 1
4
4 6 7 -1

-----Example Output-----
inf
4
impossible

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded