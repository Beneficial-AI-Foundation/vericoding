Write a program that reads two numbers $X$ and $K$. The program first finds the factors of $X$ and then gives the sum of $K$th power of every factor. The program also finds the factor of $k$ and outputs the sum of $X$ times of every factor. 

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input, two integers $X, R$. 

-----Output:-----
For each testcase, output in a single line the factors of $X$ and the $K$th power of every factor, seperated by a space.

-----Constraints-----
- $1 \leq T \leq 1000$
- $2 \leq X, K \leq 10^9$

-----Sample Input:-----
1
8 6

-----Sample Output:-----
266304 88

-----EXPLANATION:-----
Factors of x = 8 are 2, 4, and 8. Also, factors of k = 6 are 2, 3, and 6.
2^6 + 4^6 + 8^6 = 266304 and 2 × 8 + 3 × 8 + 6 × 8 = 88.
(Where a ^b denotes a raised to the power of b).

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
