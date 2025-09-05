Chefina has two sequences $A_1, A_2, \ldots, A_N$ and $B_1, B_2, \ldots, B_N$. She views two sequences with length $N$ as identical if, after they are sorted in non-decreasing order, the $i$-th element of one sequence is equal to the $i$-th element of the other sequence for each $i$ ($1 \le i \le N$).
To impress Chefina, Chef wants to make the sequences identical. He may perform the following operation zero or more times: choose two integers $i$ and $j$ $(1 \le i,j \le N)$ and swap $A_i$ with $B_j$. The cost of each such operation is $\mathrm{min}(A_i, B_j)$.
You have to find the minimum total cost with which Chef can make the two sequences identical.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.
- The third line contains $N$ space-separated integers $B_1, B_2, \ldots, B_N$.

-----Output-----
For each test case, print a single line containing one integer ― the minimum cost, or $-1$ if no valid sequence of operations exists.

-----Constraints-----
- $1 \le T \le 2,000$
- $1 \le N \le 2 \cdot 10^5$
- $1 \le A_i, B_i \le 10^9$ for each valid $i$
- the sum of $N$ over all test cases does not exceed $2 \cdot 10^6$

-----Subtasks-----
Subtask #1 (15 points):
- $T \le 20$
- $N \le 20$
Subtask #2 (85 points): original constraints

-----Example Input-----
3
1
1
2
2
1 2
2 1
2
1 1
2 2

-----Example Output-----
-1
0
1

-----Explanation-----
Example case 1: There is no way to make the sequences identical, so the answer is $-1$.
Example case 2: The sequence are identical initially, so the answer is $0$.
Example case 3: We can swap $A_1$ with $B_2$, which makes the two sequences identical, so the answer is $1$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded