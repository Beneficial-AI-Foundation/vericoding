Chef got in the trouble! He is the king of Chefland and Chessland. There is one queen in Chefland and one queen in Chessland and they both want a relationship with him. Chef is standing before a difficult choice…
Chessland may be considered a chessboard with $N$ rows (numbered $1$ through $N$) and $M$ columns (numbered $1$ through $M$). Let's denote a unit square in row $r$ and column $c$ by $(r, c)$. Chef lives at square $(X, Y)$ of this chessboard.
Currently, both queens are living in Chessland too. Each queen, when alone on the chessboard, can see all squares that lie on the same row, column or diagonal as itself. A queen from $(x_q, y_q)$ cannot see a square $(r, c)$ if the square $(X, Y)$ is strictly between them. Of course, if the queens can see each other, the kingdom will soon be in chaos!
Help Chef calculate the number of possible configurations of the queens such that the kingdom will not be in chaos. A configuration is an unordered pair of distinct squares $(x_{q1}, y_{q1})$ and $(x_{q2}, y_{q2})$ such that neither of them is the square $(X, Y)$. Two configurations are different if the position of queen $1$ is different or the position of queen $2$ is different.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains four space-separated integers $N$, $M$, $X$ and $Y$. 

-----Output-----
For each test case, print a single line containing one integer — the number of configurations such that the kingdom will not be in chaos.

-----Constraints-----
- $1 \le T \le 1000$
- $1 \le X \le N \le 10^2$
- $1 \le Y \le M \le 10^2$
- $2 \le N, M$

-----Example Input-----
2
3 3 2 2
4 4 2 3

-----Example Output-----
24
94

-----Explanation-----
Example case 1: Half of these configurations are:
- $(1, 1), (3, 3)$
- $(1, 1), (2, 3)$
- $(1, 1), (3, 2)$
- $(1, 2), (3, 3)$
- $(1, 2), (3, 2)$
- $(1, 2), (3, 1)$
- $(1, 3), (3, 1)$
- $(1, 3), (3, 2)$
- $(1, 3), (2, 1)$
- $(2, 1), (2, 3)$
- $(2, 1), (1, 3)$
- $(2, 1), (3, 3)$

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
