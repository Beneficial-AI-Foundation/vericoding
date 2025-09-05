Let's consider a rectangular table R consisting of N rows and M columns. Rows are enumerated from 1  to N from top to bottom. Columns are enumerated from 1 to M from left to right. Each element of R is a non-negative integer. R is called steady if the sum of elements in the ith row is not less then the sum of elements in the (i-1)th row for each i where 2 ≤ i ≤ N and the sum of elements in the Nth row is less than or equal to M. Your task is to find the number of different steady tables of size N x M modulo 1 000 000 000. 

-----Input-----
The first line of input contains a single integer T denoting number of test cases. First and the only line of each test case contains two space separated integers N and M denoting the number of rows and columns respectively.

-----Output-----
For each test case, print a single integer corresponding to the answer.

-----Constraints-----
- 1 ≤ T ≤ 10
- 1 ≤ N, M ≤ 2000

-----Subtasks-----
- Subtask 1 : 1 ≤ T ≤ 10 , 1 ≤ N,M ≤ 50 : ( 23 pts )
- Subtask 2 : 1 ≤ T ≤ 10 , 1 ≤ N,M ≤ 500 : ( 29 pts )
- Subtask 3 : 1 ≤ T ≤ 10 , 1 ≤ N,M ≤ 2000 : ( 48 pts )

-----Example-----
Input:
3
1 1
2 2
2 3
Output:
2
25
273

-----Explanation-----
Test case 1 : There are only 2 such grids possible 0 and 1.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded