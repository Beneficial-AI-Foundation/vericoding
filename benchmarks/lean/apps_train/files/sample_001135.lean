Chef has a sequence of N$N$ integers A1,A2,...,AN$A_1, A_2, ..., A_N$. 
Chef thinks that a triplet of integers (i,j,k)$(i,j,k)$ is good if 1≤i<j<k≤N$1 \leq i < j < k \leq N$ and P$P$ in the following expression contains an odd number of ones in its binary representation:
P=[Ai<<(⌊log2(Aj)⌋+⌊log2(Ak)⌋+2)]+[Aj<<(⌊log2(Ak)⌋+1)]+Ak$P = [ A_i<< (  \lfloor \log_2(A_j) \rfloor + \lfloor \log_2(A_k) \rfloor + 2 ) ] + [A_j << ( \lfloor \log_2(A_k) \rfloor + 1) ] + A_k$
The <<$<<$ operator is called left shift, x<<y$x << y$  is defined as x⋅2y$x \cdot 2^y$.
Help the Chef finding the total number of good triplets modulo 109+7$10^9 + 7$.

-----Input:-----
- The first line of the input contains a single integer T$T$ denoting the number of test cases. The description of T$T$ test cases follows.
- The first line of each test case contains a single integer N$N$. 
- The second line of each test case contains N$N$ space-separated integers A1,A2,...,AN$A_1, A_2, ..., A_N$.

-----Output:-----
For each test case, print a single line containing one integer, the number of good triplets modulo 109+7$10^9+7$.

-----Constraints:-----
- 1≤T≤103$1 \leq T \leq 10^3$
- 1≤N≤105$1\leq N \leq 10^5$
- 1≤Ai≤109$1 \leq A_i \leq 10^9$
- The sum of N$N$ over all testcases is less than 106$10^6$

-----Sample Input:-----
1
4
1 1 2 3

-----Sample Output:-----
1

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
