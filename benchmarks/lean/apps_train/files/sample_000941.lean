You may have helped Chef and prevented Doof from destroying the even numbers. But, it has only angered Dr Doof even further. However, for his next plan, he needs some time. Therefore, Doof has built $N$ walls to prevent Chef from interrupting him. You have to help Chef by telling him the number of walls he needs to destroy in order to reach Dr Doof.
Formally, the whole area can be represented as the first quadrant with the origin at the bottom-left corner. Dr. Doof is located at the origin $(0, 0)$. There are $N$ walls, the i-th wall is a straight line segment joining the points $(a_i, 0)$ and $(0, a_i)$. For every initial position of Chef $(x_j, y_j)$, find the number of walls he needs to break before reaching Doof. Obviously, chef can't start from a point on the wall. Therefore, if $(x_j, y_j)$ lies on any of the given walls, print $-1$ in a new line.

-----Input-----
- First line contains $T$, denoting the number of testcases.
- The first line of every test case contains a single integer $N$ denoting the number of walls Dr Doof has built.
- The next line contains $N$ space separated distinct integers each denoting $a_i$.
- The next line contains a single integer $Q$ denoting the number of times Chef asks for your help.
- The next $Q$ lines contains two space separated integers $x_j$ and $y_j$, each denoting the co-ordinates of the starting point of Chef.

-----Output-----
For each query, print the number of walls Chef needs to break in order to reach Dr Doof in a separate line. If Chef tries to start from a point on any of the walls, print $-1$.

-----Constraints-----
- $1 \leq T \leq 2 * 10^2$
- $1 \leq N, Q \leq 2 * 10^5$
- $1 \leq a_i \leq 10^9$
- $0 \leq x_j, y_j \leq 10^9$
- $a_1 < a_2 < a_3 < .... < a_N$
- Sum of $N$ and $Q$ over all testcases for a particular test file does not exceed $2 * 10^5$

-----Sample Input-----
1
2
1 3
5
0 0
2 0
0 4
1 1
1 2

-----Sample Output-----
0
1
2
1
-1

-----Explanation-----
The sample input can be represented by the graph given below:

If Chef starts from $(0, 0)$, he can reach Dr Doof without destroying any wall.

If Chef starts from $(2, 0)$, he has to destroy the $1st$ wall.

If Chef starts from $(0, 4)$, he has to destroy both the walls.

If Chef starts from $(1, 1)$, he has to destroy the $1st$ wall.

As $(1, 2)$ lies on the second wall, the answer is $-1$ for the last query.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded