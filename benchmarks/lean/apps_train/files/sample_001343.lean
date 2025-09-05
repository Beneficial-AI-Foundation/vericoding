Chef's pizza is the tastiest pizza to exist, and the reason for that is his special, juicy homegrown tomatoes. 
Tomatoes can be grown in rectangular patches of any side lengths. However, Chef only has a limited amount of land. 
Consider the entire town of Chefville to be consisting of cells in a rectangular grid of positive coordinates. 
Chef own all cells (x,y)$(x, y)$ that satisfy x∗y≤N$x*y \leq N$
As an example if N=4$N = 4$, Chef owns the following cells: 
(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,1)$(1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (3, 1), (4, 1) $
Chef can only grow tomatoes in rectangular patches consisting only of cells which belong to him. Also, if he uses a cell, he must use it entirely. He cannot use only a portion of it. 
Help Chef find the number of unique patches of rectangular land that he can grow tomatoes in! Since this number can be very large, output it modulo 1000000007$1000000007$.

-----Input:-----
- The first line of the input contains T$T$, the number of test cases.
- The next T$T$ lines of input contains one integer N$N$.

-----Output:-----
For each testcase, output the number of ways modulo 1000000007$1000000007$.

-----Constraints-----
- 1≤T≤5$1 \leq T \leq 5$
- 1≤N≤1010$1 \leq N \leq 10^{10}$

-----Sample Input:-----
2
4
10000000000

-----Sample Output:-----
23
227374950

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
