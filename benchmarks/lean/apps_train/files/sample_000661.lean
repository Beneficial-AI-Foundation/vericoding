You are given two integer sequences $A_1, A_2, \ldots, A_N$ and $B_1, B_2, \ldots, B_M$. For any two sequences $U_1, U_2, \ldots, U_p$ and $V_1, V_2, \ldots, V_q$, we define
Score(U,V)=∑i=1p∑j=1qUi⋅Vj.Score(U,V)=∑i=1p∑j=1qUi⋅Vj.Score(U, V) = \sum_{i=1}^p \sum_{j=1}^q  U_i \cdot V_j \,.
You should process $Q$ queries of three types:
- $1$ $L$ $R$ $X$: Add $X$ to each of the elements $A_L, A_{L+1}, \ldots, A_R$.
- $2$ $L$ $R$ $X$: Add $X$ to each of the elements $B_L, B_{L+1}, \ldots, B_R$.
- $3$: Print $Score(A, B)$ modulo $998,244,353$.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains two integers, $N$ and $M$, denoting the length of $A$ and $B$ respectively.
- The second line contains $N$ integers, elements of $A$.
- The third line contains $M$ integers, elements of $B$.
- The next line will contain an integer, $Q$, number of queries.
- Each of the next $Q$ lines will contain one of $3$ kinds of updates as mentioned in the statement
It’s guaranteed that each update is a valid update operation.

-----Output-----
For each query of the third type, print a single line containing one integer - the answer to that query.

-----Constraints-----
- $1 \le T \le 10$
- $2 \le N, M, Q \le 10^5$
- $0 \le |A_i|, |B_i|, |X| \le 10^5$

-----Example Input-----
1
3 4
2 -1 5
3 3 2 4
6
3
1 2 3 -2
3
1 1 3 1
2 2 4 2
3

-----Example Output-----
72
24
90

-----Explanation-----
Before the first operation, $A = [2, -1, 5],\ B = [3, 3, 2, 4]$
So, for the first operation,
$Score(A,\ B) = 2*3 + 2*3 + 2*2 + 2*4$ $+ (-1)*3$ $+ (-1)*3$ $+ (-1)*2$ $+$ $(-1)*4$ $+  5*3$ $+ 5*3$ $+ 5*2$ $+ 5*4$ $= 72.$
After the second query $A = [2, -3, 3]$, $B = [3, 3, 2, 4]$
So, for the third query, $Score(A, B) = 2*3 + 2*3 + 2*2$ $+ 2*4$ $+ (-3)*3$ $+ (-3)*3$ $+ (-3)*2$ $+ (-3)*4$ $+  3*3$ $+ 3*3$ $+ 3*2$ $+ 3*4$ $= 24$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
