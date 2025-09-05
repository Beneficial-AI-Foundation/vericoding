You are given a sequence $A_1, A_2, \ldots, A_N$. You have to split the array into maximum number of non-empty subarrays such that the gcd of elements of each subarray is equal to 1.

-----Input:-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output:-----
For each test case, print a single line containing one integer ― the maximum number of subarrays formed, or $-1$ if the array cannot be split while satisfying the above condition.

-----Constraints-----
- $1 \le T \le 3$
- $1 \le N \le 5 \cdot 10^5$
- $1 \le A_i \le 10^6$ for each valid $i$

-----Sample Input:-----
2
3
2 2 3
4
2 3 3 2

-----Sample Output:-----
1
2

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
