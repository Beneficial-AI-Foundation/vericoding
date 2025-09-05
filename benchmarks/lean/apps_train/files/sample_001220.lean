The chef was playing with numbers and he found that natural number N can be obtained by sum various unique natural numbers, For challenging himself chef wrote one problem statement, which he decided to solve in future.
Problem statement: N can be obtained as the sum of Kth power of integers in multiple ways, find total number ways?
After that Cheffina came and read what chef wrote in the problem statement, for having some fun Cheffina made some changes in the problem statement as.
New problem statement: N can be obtained as the sum of Kth power of unique +ve integers in multiple ways, find total number ways?
But, the chef is now confused, how to solve a new problem statement, help the chef to solve this new problem statement.

-----Input:-----
- First-line will contain $T$, the number of test cases. Then the test cases follow. 
- Each test case contains a single line of input, two integers $N, K$. 

-----Output:-----
For each test case, output in a single line answer to the problem statement.

-----Constraints-----
- $1 \leq T \leq 10$
- $1 \leq N \leq 1000$
- $1 \leq K \leq 6$

-----Sample Input:-----
2
4 1
38 2

-----Sample Output:-----
2
1

-----EXPLANATION:-----
For 1) 4 can be obtained by as [ 4^1 ], [1^1, 3^1], [2^1, 2^1]. (here ^ stands for power)
But here [2^1, 2^1] is not the valid way because it is not made up of unique +ve integers. 
For 2) 38 can be obtained in the way which is [2^2, 3^2, 5^2] = 4 + 9 + 25

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
