Chef has $K$ chocolates and he wants to distribute them to $N$ people (numbered $1$ through $N$). These people are standing in a line in such a way that for each $i$ ($1 \le i \le N-1$), person $i$ and person $i+1$ are adjacent.
First, consider some way to distribute chocolates such that for each valid $i$, the number of chocolates the $i$-th person would receive from Chef is $A_i$ and the sum $S_1 = \sum_{i=1}^{N-1} \left|A_i - A_{i+1}\right|$ is minimum possible. Of course, each person must receive a non-negative integer number of chocolates.
Then, Chef wants to create a new sequence $B_1, B_2, \ldots, B_N$ by rearranging (permuting) the elements of the sequence $A_1, A_2, \ldots, A_N$. For each valid $i$, the number of chocolates the $i$-th person actually receives from Chef is $B_i$. Chef wants to distribute the chocolates (choose $B_1, B_2, \ldots, B_N$ by permuting the sequence $A$ and give $B_i$ chocolates to the $i$-th person for each valid $i$) in such a way that $S_2 = \sum_{i=1}^{N-1} \left|B_i – B_{i+1}\right|$ is maximum possible. You need to find the maximum value of $S_2$.
It is guaranteed that $S_2$ does not depend on the exact choice of the sequence $A_1, A_2, \ldots, A_N$, as long as it is a sequence that minimises $S_1$.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains a single integer $K$.

-----Output-----
For each test case, print a single line containing one integer — the maximum value of the sum $S_2$.

-----Constraints-----
- $1 \le T \le 10$
- $2 \le N \le 10^5$
- $2 \le K \le 10^{100,000}$

-----Subtasks-----
Subtask #1 (30 points): $2 \le N, K \le 1,000$
Subtask #2 (70 points): original constraints

-----Example Input-----
1
3
2

-----Example Output-----
2

-----Explanation-----
Example case 1: To minimise $S_1$, Chef could give $1$ chocolate to person $1$ and $1$ chocolate to person $2$, so $S_1 = |1-1| + |1-0| = 1$.
To maximise $S_2$, Chef can give $1$ chocolate to person $1$ and $1$ chocolate to person $3$, since the sequence $B = (1, 0, 1)$ is a permutation of $A = (1, 1, 0)$. Then, $S_2 = |1-0| + |0-1| = 2$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
