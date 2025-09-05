Raj is a math pro and number theory expert. One day, he met his age-old friend Chef. Chef claimed to be better at number theory than Raj, so Raj gave him some fuzzy problems to solve. In one of those problems, he gave Chef a 3$3$-tuple of non-negative integers (a0,b0,c0)$(a_0, b_0, c_0)$ and told Chef to convert it to another tuple (x,y,z)$(x, y, z)$.
Chef may perform the following operations any number of times (including zero) on his current tuple (a,b,c)$(a, b, c)$, in any order:
- Choose one element of this tuple, i.e. a$a$, b$b$ or c$c$. Either add 1$1$ to that element or subtract 1$1$ from it. The cost of this operation is 1$1$.
- Merge: Change the tuple to (a−1,b−1,c+1)$(a-1, b-1, c+1)$, (a−1,b+1,c−1)$(a-1, b+1, c-1)$ or (a+1,b−1,c−1)$(a+1, b-1, c-1)$, i.e. add 1$1$ to one element and subtract 1$1$ from the other two. The cost of this operation is 0$0$.
- Split: Change the tuple to (a−1,b+1,c+1)$(a-1, b+1, c+1)$, (a+1,b−1,c+1)$(a+1, b-1, c+1)$ or (a+1,b+1,c−1)$(a+1, b+1, c-1)$, i.e. subtract 1$1$ from one element and add 1$1$ to the other two. The cost of this operation is also 0$0$.
After each operation, all elements of Chef's tuple must be non-negative. It is not allowed to perform an operation that would make one or more elements of this tuple negative.
Can you help Chef find the minimum cost of converting the tuple (a0,b0,c0)$(a_0, b_0, c_0)$ to the tuple (x,y,z)$(x, y, z)$? It can be easily proved that it is always possible to convert any tuple of non-negative integers to any other.

-----Input-----
- The first line of the input contains a single integer T$T$ denoting the number of test cases. The description of T$T$ test cases follows.
- The first and only line of each test case contains six space-separated integers a0$a_0$, b0$b_0$, c0$c_0$, x$x$, y$y$ and z$z$.

-----Output-----
For each test case, print a single line containing one integer ― the minimum cost.

-----Constraints-----
- 1≤T≤105$1 \le T \le 10^5$
- 0≤a0,b0,c0,x,y,z≤1018$0 \le a_0, b_0, c_0, x, y, z \le 10^{18}$

-----Subtasks-----
Subtask #1 (20 points): 0≤a0,b0,c0,x,y,z≤100$0 \le a_0, b_0, c_0, x, y, z \le 100$
Subtask #2 (80 points): original constraints

-----Example Input-----
2
1 1 1 2 2 2
1 2 3 2 4 2

-----Example Output-----
0
1

-----Explanation-----
Example case 1: The tuple (1,1,1)$(1, 1, 1)$ can be converted to (2,2,2)$(2, 2, 2)$ using only three Split operations, with cost 0$0$: (1,1,1)→(2,0,2)→(1,1,3)→(2,2,2)$(1, 1, 1) \rightarrow (2, 0, 2) \rightarrow (1, 1, 3) \rightarrow (2, 2, 2)$.
Example case 2: We can use one addition operation and one Split operation: (1,2,3)→(1,3,3)→(2,4,2)$(1, 2, 3) \rightarrow (1, 3, 3) \rightarrow (2, 4, 2)$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible