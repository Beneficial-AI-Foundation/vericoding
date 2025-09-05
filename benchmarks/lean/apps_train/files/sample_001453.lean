You are given a grid with dimension $n$ x $m$ and two points with coordinates $X(x1,y1)$ and $Y(x2,y2)$ . Your task is to find the number of ways in which one can go from point $A(0, 0)$ to point $B (n, m)$ using the $shortest$ possible path such that the shortest path neither passes through $X$ nor through $Y$. 

Consider the above 4 x 4 grid . Our shortest path can't pass through points (1,3) and (3,3) (marked by yellow dots). One of the possible shortest path is from $A$ to $C$ and then from $C$ to $B$.

-----Input:-----
- First line contains $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input, six space separated integers $n, m, x1, y1, x2, y2$. 

-----Output:-----
- For each testcase, output in a single line number of ways modulo $998244353$.

-----Constraints-----
- $1 \leq T \leq 10^5$
- $3 \leq n,m \leq 10^5$
- $1 \leq x1, x2 \leq n - 1$
- $1 \leq y1, y2 \leq m - 1$
- $x1 \leq x2$
- $y1 \leq y2$
- $X$ and $Y$ never coincide.

-----Sample Input:-----
1
3 3 1 1 1 2

-----Sample Output:-----
5

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded