The Golomb sequence $G_1, G_2, \ldots$ is a non-decreasing integer sequence such that for each positive integer $n$, $G_n$ is the number of occurrences of $n$ in this sequence. The first few elements of $G$ are $[1, 2, 2, 3, 3, 4, 4, 4, 5, \ldots]$. Do you know the recurrence relation for the Golomb sequence? It is $G_1 = 1$ and $G_{n+1} = 1+G_{n+1-G_{G_n}}$ for each $n \ge 1$. A self-describing sequence, isn't it?
Mr. Strange wants to learn CP, so he asked Chef, who is one of the best competitive programmers in the world, to teach him. Chef decided to test his ability by giving him the following task.
Find the sum of squares of the $L$-th through $R$-th term of the Golomb sequence, i.e. $S = \sum_{i=L}^R G_i^2$. Since the sum can be quite large, compute it modulo $10^9+7$.
Can you help Mr. Strange carry out this task given to him by his teacher?

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains two space-separated integers $L$ and $R$.

-----Output-----
For each test case, print a single line containing one integer $S$ modulo $10^9+7$.

-----Constraints-----
- $1 \le T \le 10^5$
- $1 \le L \le R \le 10^{10}$

-----Subtasks-----
Subtask #1 (50 points):
- $T \le 10^2$
- $R \le 10^9$
Subtask #2 (50 points): original constraints

-----Example Input-----
3
1 5
2 4
100 100

-----Example Output-----
27
17
441

-----Explanation-----
Example case 1: $1^2 + 2^2 + 2^2 + 3^2 + 3^2 = 27$
Example case 2: $2^2 + 2^2 + 3^2 = 17$
Example case 3: $21^2 = 441$

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded