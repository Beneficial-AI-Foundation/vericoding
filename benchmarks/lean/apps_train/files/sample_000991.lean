There are $N$ cities on a circle, numbered $1$ through $N$. For each $i$ ($1 \le i \le N-1$), cities $i$ and $i+1$ are directly connected by a bidirectional road with length $A_i$, and cities $N$ and $1$ are also directly connected by a bidirectional road with length $A_N$. However, we do not know the lengths of some roads.
For each city $i$, we do know that it has an opposite city — formally, there is a city $j \neq i$ such that the clockwise distance between cities $i$ and $j$ is equal to the counterclockwise distance between these cities.
Please find the lengths of all roads in such a way that the above condition is satisfied and the sum of lengths of all roads is minimised.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of the input contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \dots, A_N$. For each valid $i$, $A_i = -1$ denotes that the length of road $i$ is unknown.

-----Output-----
For each test case, print a line containing the string "NO" if there is no solution or "YES" otherwise. If a solution exists, print a second line containing $N$ space-separated positive integers — the lengths of all roads in your solution. Each of these integers should be $\le 10^9$. If there are multiple solutions, you may print any one.

-----Constraints-----
- $1 \le T \le 100$
- $3 \le N \le 10^5$
- $1 \le A_i \le 10^9$ or $A_i = -1$ for each valid $i$
- the sum of $N$ for all test cases does not exceed $3\cdot 10^5$

-----Subtasks-----
Subtask #1 (10 points): $N \le 4$
Subtask #2 (20 points): $A_i = \pm 1$ for each valid $i$
Subtask #3 (70 points): original constraints

-----Example Input-----
4
4
1 1 1 1
4
1 1 1 2
4
1 -1 -1 4
4
1 -1 2 -1

-----Example Output-----
YES
1 1 1 1
NO
YES
1 4 1 4
NO

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded