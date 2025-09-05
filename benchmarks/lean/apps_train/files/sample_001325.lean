Chef made $N$ pieces of cakes, numbered them $1$ through $N$ and arranged them in a row in this order. There are $K$ possible types of flavours (numbered $1$ through $K$); for each valid $i$, the $i$-th piece of cake has a flavour $A_i$.
Chef wants to select a contiguous subsegment of the pieces of cake such that there is at least one flavour which does not occur in that subsegment. Find the maximum possible length of such a subsegment of cakes.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains two integers $N$ and $K$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
For each test case, print a single line containing one integer ― the maximum length of a valid subsegment.

-----Constraints-----
- $1 \le T \le 1,000$
- $1 \le N \le 10^5$
- $2 \le K \le 10^5$
- $1 \le A_i \le K$ for each valid $i$
- the sum of $N$ over all test cases does not exceed $10^6$

-----Subtasks-----
Subtask #1 (50 points):
- $N \le 10^3$
- $K = 2$
- the sum of $N$ over all test cases does not exceed $10^4$
Subtask #2 (50 points): original constraints

-----Example Input-----
2
6 2
1 1 1 2 2 1
5 3
1 1 2 2 1

-----Example Output-----
3
5

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
