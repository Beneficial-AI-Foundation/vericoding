You are given a sequence $A_1, A_2, \ldots, A_N$. You may perform the following operation an arbitrary number of times (including zero): choose two adjacent elements of this sequence, i.e. $A_i$, $A_{i+1}$ for some valid $i$, and swap them. However, for each valid $i$, it is not allowed to choose $A_i$ (the element with the index $i$, regardless of its value at any point in time) more than once in total during this process.
Find the maximum of the sum $S = \sum_{i=1}^N A_i \cdot i$.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
For each test case, print a single line containing one integer ― the maximum possible value of $S$.

-----Constraints-----
- $1 \le T \le 1,000$
- $1 \le N \le 10^5$
- $1 \le A_i \le 10^9$ for each valid $i$
- the sum of $N$ over all test cases does not exceed $10^6$

-----Subtasks-----
Subtask #1 (50 points):
- $N \le 20$
- the sum of $N$ over all test cases does not exceed $200$
Subtask #2 (50 points): original constraints

-----Example Input-----
2
4
2 1 4 3
4
7 6 3 2

-----Example Output-----
30
39

-----Explanation-----
Example case 1: Swap the first and second element of the initial sequence. Then, swap the third and fourth element of the resulting sequence. The final sequence $A$ is $(1, 2, 3, 4)$.
Example case 2: Swap the second and third element to make the sequence $(7, 3, 6, 2)$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded