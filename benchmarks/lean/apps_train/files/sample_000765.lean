One of Chef's friends offered him a deal: during $D$ days, they are going to exchange money. For each $i$ ($1 \le i \le D$), on the $i$-th day, Chef's friend would give Chef $A$ rupees, while Chef would give his friend $2^{i-1}$ rupees ($1$ rupee on day $1$, $2$ rupees on day $2$, $4$ rupees on day $3$, and so on). Chef's profit from the deal is the total number of rupees he received from his friend minus the total number of rupees he gave his friend.
Chef decided to ask for your advice before accepting the deal. You want to help him by telling him two numbers $D_1$ and $D_2$, where $D_1$ is the maximum value of $D$ such that Chef should accept the deal, i.e. his profit from the deal is positive if $D = D_1$, and $D_2$ is the value of $D$ that leads to the maximum possible profit for Chef. If there are multiple values of $D$ that lead to the maximum profit, $D_2$ is the smallest of these values.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains a single integer $A$.

-----Output-----
For each test case, print a single line containing two space-separated integers $D_1$ and $D_2$.

-----Constraints-----
- $1 \le T \le 100,000$
- $5 \le A \le 10^9$

-----Subtasks-----
Subtask #1 (100 points): original constraints

-----Example Input-----
4
5
8
9
1000000000

-----Example Output-----
4 3
5 3
5 4
35 30

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible