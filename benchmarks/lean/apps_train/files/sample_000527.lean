"Humankind cannot gain anything without first giving something in return. To obtain, something of equal value must be lost. That is alchemy's first law of Equivalent Exchange. In those days, we really believed that to be the world's one, and only truth."
-- Alphonse Elric
Now, here we have an equivalent exchange law for triangles which states that two right-angled isosceles triangles of the same color can be made into a square of the same color using Alchemy.
You are given N$N$ right-angled isosceles colored triangles numbered from 1$1$ to N$N$. For each triangle, the two equal sides have a length of 1$1$ unit. The Color of i$i$-th triangle is given by Ci$C_i$.
To create a tower, we choose some consecutive (2×k)+1$2 \times k)+1$ triangles for any k≥0$k \geq 0$. We then pick some 2×k$2 \times k$ of them (these need not be consecutive), and form k$k$ pairs of triangles such that both triangles in pair have the same color. Also, each of the 2×k$2 \times k$ should be in exactly one pair. Then the two triangles in each pair are joined using Alchemy (following the law of equivalent exchange for triangles) to form squares and these k$k$ squares are placed one upon other. The one remaining triangle is placed as a roof to the tower. This results in a tower of the height of k$k$.
Find the maximum height of the tower that can be formed. 
In other words, you should select the largest consecutive segment of triangles, such that you can form a tower using every single one of those triangles. In particular, you leave out one triangle, which will form the roof, and the other triangles should all be paired up such that both triangles in a pair have the same colour.

-----Input:-----
- The first line contains T$T$, the number of test cases. Then the test cases follow. 
- For every test case, the first line contains N$N$ denoting the number of triangles.
- For every test case, the second line contains N$N$ space-separated integers Ci$C_{i}$ denoting the color of the triangles. ( 1≤i≤N$1 \leq i \leq N$).

-----Output:-----
For every test case, output a single integer denoting the maximum height of the tower that can be formed.

-----Constraints-----
- 1≤T≤100$1 \leq T \leq 100$ 
- 1≤N≤105$1 \leq N \leq 10^{5}$ 
- 1≤Ci≤30$1 \leq C_{i} \leq 30$ 
- Sum of N$N$ over all test cases doesn't exceed 5×105$5\times 10^{5}$ 

-----Sample Input:-----
4
14
5 4 2 2 3 2 1 3 2 7 4 9 9 9
3
1 2 1
3
1 1 1
5
1 2 3 4 1

-----Sample Output:-----
3
1
1
0

-----EXPLANATION:-----
- #1$1$: The subarray [2,2,3,2,1,3,2]$[2, 2, 3, 2, 1, 3, 2]$ results in a tower of height 3$3$.
- #2$2$: The subarray [1,2,1]$[ 1, 2, 1 ]$ results in a tower of height 1$1$.
- #3$3$: The subarray [1,1,1]$[ 1, 1, 1 ]$ results in a tower of height 1$1$. 
- #4$4$: The subarrays [1]$[ 1 ]$, [2]$[ 2 ]$ , [3]$[ 3 ]$, [4]$[ 4 ]$ and [1]$[ 1 ]$ all results in a tower of height 0$0$.

The above tower is possible by subarray [2,2,3,2,1,3,2]$[2, 2, 3, 2, 1, 3, 2]$ resulting in a height of 3$3$ in test case 1$1$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded