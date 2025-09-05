Chef has a sequence $A_1, A_2, \ldots, A_N$. For a positive integer $M$, sequence $B$ is defined as $B = A*M$ that is, appending $A$ exactly $M$ times. For example, If $A = [1, 2]$ and $M = 3$, then $B = A*M = [1, 2, 1, 2, 1, 2]$
You have to help him to find out the minimum value of $M$ such that the length of the longest strictly increasing subsequence is maximum possible.

-----Input:-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output:-----
For each test case, print a single line containing one integer ― the minimum value of $M$.

-----Constraints-----
- $1 \le T \le 500$
- $1 \le N \le 2*10^5$
- $1 \le A_i \le 10^9$
- It's guaranteed that the total length of the sequence $A$ in one test file doesn't exceed $2*10^6$

-----Sample Input:-----
3
2
2 1
2
1 2
5
1 3 2 1 2

-----Sample Output:-----
2
1
2

-----Explanation:-----
In the first test case, Choosing $M = 2$ gives $B = [2, 1, 2, 1]$ which has a longest strictly increasing sequence of length $2$ which is the maximum possible.
In the second test case, Choosing $M = 1$ gives $B  = [1, 2]$ which has a longest strictly increasing sequence of length $2$ which is the maximum possible.

def find_min_m (arr : List Int) (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded