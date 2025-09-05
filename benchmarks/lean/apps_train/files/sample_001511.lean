A matrix B (consisting of integers) of dimension N × N is said to be good if there exists an array A (consisting of integers) such that B[i][j]  = |A[i] - A[j]|, where |x| denotes absolute value of integer x.
You are given a partially filled matrix B of dimension N × N. Q of the entries of this matrix are filled by either 0 or 1. You have to identify whether it is possible to fill the remaining entries of matrix B (the entries can be filled by any integer, not necessarily by 0 or 1) such that the resulting fully filled matrix B is good.

-----Input-----
The first line of the input contains an integer T denoting the number of test cases. 
The first line of each test case contains two space separated integers N, Q.
Each of the next Q lines contain three space separated integers i, j, val, which means that B[i][j] is filled with value val.

-----Output-----
For each test case, output "yes" or "no" (without quotes) in a single line corresponding to the answer of the problem.

-----Constraints-----
- 1 ≤ T ≤ 106
- 2 ≤ N ≤ 105
- 1 ≤ Q ≤ 106
- 1 ≤ i, j ≤ N
- 0 ≤ val ≤ 1
- Sum of each of N, Q over all test cases doesn't exceed 106

-----Subtasks-----
- Subtask #1 (40 points) 2 ≤ N ≤ 103, 1 ≤ Q ≤ 103, Sum of each of N, Q over all test cases doesn't exceed 104
- Subtask #2 (60 points) Original Constraints

-----Example-----
Input
4
2 2
1 1 0
1 2 1
2 3
1 1 0
1 2 1
2 1 0
3 2
2 2 0
2 3 1
3 3
1 2 1
2 3 1
1 3 1

Output
yes
no
yes
no

-----Explanation-----
Example 1. You can fill the entries of matrix B as follows. 

0 1
1 0
This matrix corresponds to the array A = [1, 2].

Example 2. It is impossible to fill the remaining entries of matrix B such that the resulting matrix is good, as B[1][2] = 1 and B[2][1] = 0, which is impossible.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded