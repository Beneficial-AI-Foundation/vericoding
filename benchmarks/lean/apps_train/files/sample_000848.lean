Appy and Chef are participating in a contest. There are $N$ problems in this contest; each problem has a unique problem code between $1$ and $N$ inclusive. Appy and Chef decided to split the problems to solve between them ― Appy should solve the problems whose problem codes are divisible by $A$ but not divisible by $B$, and Chef should solve the problems whose problem codes are divisible by $B$ but not divisible by $A$ (they decided to not solve the problems whose codes are divisible by both $A$ and $B$).
To win, it is necessary to solve at least $K$ problems. You have to tell Appy whether they are going to win or lose.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains four space-separated integers $N$, $A$, $B$ and $K$.

-----Output-----
For each test case, print a single line containing the string "Win" if they can solve at least $K$ problems or "Lose" otherwise (without quotes).

-----Constraints-----
- $1 \le T \le 15$
- $1 \le K \le N \le 10^{18}$
- $1 \le A, B \le 10^9$

-----Subtasks-----
Subtask #1 (15 points):
- $1 \le T \le 15$
- $1 \le K \le N \le 10^6$
- $1 \le A, B \le 10^3$
Subtask #2 (85 points): original constraints

-----Example Input-----
1
6 2 3 3

-----Example Output-----
Win

-----Explanation-----
Example case 1: Appy is solving the problems with codes $2$ and $4$, Chef is solving the problem with code $3$. Nobody is solving problem $6$, since $6$ is divisible by both $2$ and $3$. Therefore, they can solve $3$ problems and win.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
