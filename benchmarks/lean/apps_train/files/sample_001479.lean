Sereja has two integers — A and B — in 7-ary system. He wants to calculate the number C, such that B * C = A. It is guaranteed that B is a divisor of A.

Please, help Sereja calculate the number C modulo 7L.

-----Input-----

First line of input contains an integer T — the number of test cases. T tests follow.

For each test case, the first line contains the integer A, and the second line contains the integer B, and the third line contains the integer L. A and B are given in 7-ary system.

-----Output-----
Output the answer in 7-ary system.

-----Constraints-----
- 1 ≤ T ≤ 10
- A and B are both positive integers.
- Length of A is a positive integer and doesn't exceed 106.
- L and length of B are positive integers and do not exceed 10000.

-----Subtasks-----
- Sub task #1 (20 points): Length of A is a positive integer and doesn't exceed 20.
- Sub task #2 (30 points): Length of A is a positive integer and doesn't exceed 2000.
- Sub task #3 (50 points): Original constraints.

-----Example-----
Input:3
21
5
10
202
13
1
202
13
2

Output:3
3
13

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
