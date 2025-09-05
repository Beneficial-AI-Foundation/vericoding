The Fibonacci sequence $F_0, F_1, \ldots$ is a special infinite sequence of non-negative integers, where $F_0 = 0$, $F_1 = 1$ and for each integer $n \ge 2$, $F_n = F_{n-1} + F_{n-2}$.
Consider the sequence $D$ of the last decimal digits of the first $N$ Fibonacci numbers, i.e. $D = (F_0 \% 10, F_1 \% 10, \ldots, F_{N-1} \% 10)$. Now, you should perform the following process:
- Let $D = (D_1, D_2, \ldots, D_l)$.
- If $l = 1$, the process ends.
- Create a new sequence $E = (D_2, D_4, \ldots, D_{2 \lfloor l/2 \rfloor})$. In other words, $E$ is the sequence created by removing all odd-indexed elements from $D$.
- Change $D$ to $E$.
When this process terminates, the sequence $D$ contains only one number. You have to find this number.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains a single integer $N$.

-----Output-----
For each test case, print a single line containing one integer ― the last remaining number.

-----Constraints-----
- $1 \le T \le 10^5$
- $1 \le N \le 10^{18}$

-----Subtasks-----
Subtask #1 (20 points):
- $1 \le T \le 10^5$
- $1 \le N \le 10^7$
Subtask #2 (80 points): original constraints

-----Example Input-----
1
9

-----Example Output-----
3

-----Explanation-----
Example case 1: The first $N$ Fibonacci numbers are $(0, 1, 1, 2, 3, 5, 8, 13, 21)$. The sequence $D$ is $(0, 1, 1, 2, 3, 5, 8, 3, 1) \rightarrow (1, 2, 5, 3) \rightarrow (2, 3) \rightarrow (3)$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded