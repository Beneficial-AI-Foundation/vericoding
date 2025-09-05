You are given two binary strings $S$ and $P$, each with length $N$. A binary string contains only characters '0' and '1'. For each valid $i$, let's denote the $i$-th character of $S$ by $S_i$.
You have to convert the string $S$ into $P$ using zero or more operations. In one operation, you should choose two indices $i$ and $j$ ($1 \leq i < j \leq N$) such that $S_i$ is '1' and $S_j$ is '0', and swap $S_i$ with $S_j$.
Determine if it is possible to convert $S$ into $P$ by performing some operations.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains a single string $S$.
- The third line contains a single string $P$.

-----Output-----
For each test case, print a single line containing the string "Yes" if it is possible to convert $S$ into $P$ or "No" otherwise (without quotes).

-----Constraints-----
- $1 \leq T \leq 10^5$
- $1 \leq N \leq 10^5$
- $S$ and $P$ contain only characters '0' and '1'
- the sum of $N$ over all test cases does not exceed $10^5$

-----Subtasks-----
Subtask #1 (20 points):
- $N \leq 14$
- the sum of $N$ over all test cases does not exceed $100$
Subtask #2 (30 points): the sum of $N$ over all test cases does not exceed $1,000$
Subtask #3 (50 points): original constraints

-----Example Input-----
3
2
00
00
3
101
010
4
0110
0011

-----Example Output-----
Yes
No
Yes

-----Explanation-----
Example case 1: The strings are already equal.
Example case 2: It can be showed that it is impossible to convert $S$ into $P$.
Example case 3: You can swap $S_2$ with $S_4$. The strings will then be equal.

def can_convert_binary_strings (s p : String) : String := sorry

def count_ones (s : String) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
