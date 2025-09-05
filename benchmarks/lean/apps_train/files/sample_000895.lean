Doctor Kunj installed new software on cyborg Shresth.
This software introduced Shresth to range minimum queries.
Cyborg Shresth thought of T$T$ different problems in each of which you will be given
an array A$A$ of length N$N$ and an array B$B$ of length M$M$. In each of these problems, you have to calculate:
∑mi=1∑mj=irangeMin(B[i],B[j])$\sum_{i=1}^m \sum_{j=i}^m rangeMin(B[i],B[j])$
Where rangeMin(i,j)$rangeMin(i,j)$ returns the minimum element in the range of indices i$i$ to j$j$ (both included) in array A$A$.
It is given that array B$B$ consists of pairwise distinct elements and is in ascending order.

-----Input Format:-----
- First line will contain T$T$, the number of different problems Cyborg Shresth thought of.
- Each problem's input data will be given in three different lines. 
- The first line will contain N$N$ and M$M$, the length of array A$A$ and B$B$ respectively. 
- The second line will contain N$N$ space separated positive integers, which form the array A$A$. - 
- The third line will contain M$M$ space separated positive integers, which form the array B$B$.

-----Output Format:-----
- For each different problem, print on a new line the answer to the problem, i.e. the value of ∑mi=1∑mj=irangeMin(B[i],B[j])$\sum_{i=1}^m \sum_{j=i}^m rangeMin(B[i],B[j])$ .

-----Constraints:-----
- 1≤T≤105$1 \leq T \leq {10}^5$
- 1≤N≤105$1 \leq N \leq {10}^5$
- 1≤M≤105$1 \leq M \leq {10}^5$
- 1≤A[i]≤109$1 \leq A[i] \leq 10^9$
- 1≤B[i]≤N$1 \leq B[i] \leq N$
It is guaranteed that the sum of N$N$ over all test cases does not exceed 106${10}^6$ .

-----Sample Input:-----
1
7 3
10 3 7 9 1 19 2
1 4 6

-----Sample Output:-----
43

-----Explanation:-----
For the given array A$A$, we have to calculate rangeMin(1,1)+rangeMin(1,4)+rangeMin(1,6)+rangeMin(4,4)+rangeMin(4,6)+rangeMin(6,6)$rangeMin(1,1) + rangeMin(1,4) + rangeMin(1,6) + rangeMin(4,4) + rangeMin(4,6) + rangeMin(6,6) $.
This is equal to 10+3+1+9+1+19=43$10 + 3 + 1 + 9 + 1 +19 = 43$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded