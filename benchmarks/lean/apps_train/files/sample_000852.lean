Rachel has some candies and she decided to distribute them among $N$ kids. The ith kid receives $A_i$ candies. The kids are happy iff the difference between the highest and lowest number of candies received is less than $X$.
Find out if the children are happy or not.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- The first line contains $N$ and $X$. 
- The second line contains $N$ integers $A_1,A_2,...,A_N$. 

-----Output:-----
For each test case print either "YES"(without quotes) if the kids are happy else "NO"(without quotes)

-----Constraints-----
- $1 \leq T \leq 100$
- $1 \leq N, X \leq 10^5$
- $1 \leq A_i \leq 10^5$

-----Sample Input:-----
2

5 6

3 5 6 8 1

3 10

5 2 9

-----Sample Output:-----
NO

YES

-----EXPLANATION:-----
- Example 1: Difference between maximum and minimum candies received is 8-1=7. 7 is greater than 6, therefore, the kids are not happy.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
