Consider the infinite x$x$ axis. There are N$N$ impacts on this X-axis at integral points (X1$X_1$,X2$X_2$,....XN$X_N$)  (all distinct) . An impact at a point X$X$i propagates such that at a point X$X$0, the effect of the impact is K|Xi−X0|$K^{|X_i - X_0|}$. Given the point X0$X_0$, N$N$ and K$K$. Assume the total impact on X0$X_0$ is M$M$, find if it is possible to do so.Note: You are not required to find the set X

Formally print "yes" if this is possible and "no" if not possible.

-----Input:-----
- First line will contain T$T$, number of testcases. Then the testcases follow. 
-  Each testcase contains of a single line of input, four integers N$N$,K$K$,M$M$,X$X$0 

-----Output:-----
-  The output of each test case is either "yes" or "no"

-----Constraints -----
-  1≤T≤1000$1\leq T \leq 1000$
-  1≤N≤100$1\leq N \leq 100$
-  1≤K≤1000$1\leq K \leq 1000$
-  1≤M≤1018$1\leq M \leq 10^{18}$
-  −109≤X0≤109$-10^9 \leq X_0 \leq 10^9$ 

-----Sample Input:-----
	2

4 3 10 10

2 3 10 10

-----Sample Output:-----
	no

yes

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded