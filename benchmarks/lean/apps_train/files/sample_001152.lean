You are given a sequence of integers $A_1, A_2, \ldots, A_N$. This sequence is circular ― for each valid $i$, the element $A_{i+1}$ follows after $A_i$, and the element $A_1$ follows after $A_N$.
You may insert any positive integers at any positions you choose in this sequence; let's denote the resulting sequence by $B$. This sequence is also circular. For each pair of its elements $B_s$ and $B_f$, let's denote the (non-circular) sequence created by starting at $B_s$ and moving from each element to the one that follows after it, until we reach $B_f$, by $B(s, f)$. This sequence includes the elements $B_s$ and $B_f$.
For each $K$ from $2$ to $N$ inclusive, find the smallest possible number of elements that need to be inserted into $A$ to form a sequence $B$ for which there is no subsequence $B(p, q)$ such that:
- The size of $B(p, q)$ is at least $K$.
- There is no pair of consecutive elements in $B(p, q)$ such that their GCD is equal to $1$.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
For each test case, print a single line containing $N-1$ space-separated integers. For each $i$ ($1 \le i \le N-1$), the $i$-th of these integers should be the smallest number of inserted elements in a valid sequence $B$ for $K = i+1$.

-----Constraints-----
- $1 \le T \le 2,000$
- $2 \le N \le 10^5$
- $1 \le A_i \le 10^9$ for each valid $i$
- the sum of $N$ over all test cases does not exceed $2 \cdot 10^6$

-----Example Input-----
1
5
3 6 4 5 9

-----Example Output-----
3 1 1 0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
