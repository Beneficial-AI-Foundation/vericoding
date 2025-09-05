You are given a sequence of integers $A_1, A_2, \dots, A_N$.
You should choose an arbitrary (possibly empty) subsequence of $A$ and multiply each element of this subsequence by $-1$. The resulting sequence should satisfy the following condition: the sum of elements of any contiguous subsequence with length greater than 1 is strictly positive.
You should minimise the sum of elements of the resulting sequence. Find one such sequence with the minimum possible sum.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \dots, A_N$.

-----Output-----
For each test case, print a single line containing $N$ space-separated integers $B_1, B_2, \dots, B_N$. For each valid $i$, $B_i$ must be equal to either $A_i$ (the sign of this element did not change) or $-A_i$ (the sign of this element changed).
If there is more than one answer, you may output any one.

-----Constraints-----
- $1 \le T \le 10^5$
- $2 \le N \le 10^5$
- $1 \le A_i \le 10^9$ for each valid $i$
- the sum of $N$ for all test cases does not exceed $5 \cdot 10^5$

-----Subtasks-----
Subtask #1 (20 points):
- $1 \le T \le 200$
- $2 \le N \le 10$
Subtask #2 (30 points):
- $1 \le T \le 1,000$
- $N \le 2,000$
Subtask #3 (50 points): original constraints

-----Example Input-----
4
4
4 3 1 2
6
1 2 2 1 3 1
5
10 1 2 10 5
4
1 2 1 2

-----Example Output-----
4 3 -1 2
-1 2 2 -1 3 -1
10 -1 2 10 -5
1 2 -1 2

-----Explanation-----
Example case 1: If we change only the sign of $A_3$, we get a sequence $\{4, 3, -1, 2\}$ with sum $8$. This sequence is valid because the sums of all its contiguous subsequences with length $> 1$ are positive. (For example, the sum of elements of the contiguous subsequence $\{A_3, A_4\}$ equals $-1 + 2 = 1 > 0$.)
There are only two valid sequences $\{4, 3, -1, 2\}$ and $\{4, 3, 1, 2\}$ with sums $8$ and $10$ respectively, so this sequence has the smallest possible sum.
For instance, the sequence $\{4, -3, 1, 2\}$ isn't valid, because the sum of $\{A_2, A_3, A_4\}$ equals $-3 + 1 + 2 = 0 \le 0$.

def abs (n : Int) : Int := 
  if n < 0 then -n else n

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
