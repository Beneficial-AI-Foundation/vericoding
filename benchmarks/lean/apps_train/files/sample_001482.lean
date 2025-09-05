Prime numbers are arranged in a ordered list U$U$, in increasing order. Let S$S$ be a sublist of U$U$ with a unique property that for every element A$A$ belonging to list S$S$, if i$i$ denotes the index of A$A$ in list U$U$, than i$i$ also belongs to list U$U$.
Given N$N$, find sum of first N$N$ elements of list S$S$, assuming 1-based indexing.
As the sum can be very large, print the sum modulo 109+7$10^{9}+7$.

-----Input:-----
-The first line of the input contains a single integer T$T$ denoting the number of test cases.
-Only line of each test case has an integer N$N$ .

-----Output:-----
For each test case, print a single integer denoting the sum of first N$N$ elements of set S$S$ modulo 109+7$10^{9}+7$.

-----Constraints-----
- 1≤T≤10000$1 \leq T \leq 10000$
- 1≤N≤1000$1 \leq N \leq 1000$

-----Subtasks-----
- 
20 points : 
- 
1≤T≤10000$1 \leq T \leq 10000$
- 
1≤N≤10$1 \leq N \leq 10$
- 
20 points :
- 
1≤T≤100$1 \leq T \leq 100$
- 
1≤N≤100$1 \leq N \leq 100$
- 
60 points : Original Constraints

-----Sample Input:-----
2

1
2

-----Sample Output:-----
3
8

-----EXPLANATION:-----
Example case 1: 
First few elements of set S$S$ are  {3,5,11…}  , so sum is 3.
Example case 2: 
Sum is 3+5=8.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded