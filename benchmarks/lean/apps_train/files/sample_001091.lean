The Chef is given an array of numbers and asked to find the first balance point of an array. A balance point is an index in the array N where the sum of the integers to the left of N is equal to the sum of the integers to the right of N. If there is no such balance point, print -1

-----Input-----
The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows.
The first line of each test case contains a single integer N denoting the number of weights on the array. The second line contains N space-separated integers A1, A2, ..., AN denoting the weights

-----Output-----
For each test case, output a single line containing the index of the first balance point. If no such index exists, output -1

-----Constraints-----
For Subtask 1:
- 1 ≤ T ≤ 10
- 1 ≤ N ≤ 10
- -1000 ≤ A1, A2, ..., AN ≤ 1000
For Subtask 1:
- 1 ≤ T ≤ 10
- 1 ≤ N ≤ 1000
- -10000 ≤ A1, A2, ..., AN ≤ 10000

-----Example-----
Input:
2
7
7 8 9 1 9 8 7
6
1 100 50 -51 1 1

Output:
3
1

-----Explanation-----
Example case 1. In the first case, at the midpoint of the array 1, the sum of the left side {7,8,9} is equal to the sum of the right side {9,8,7}
Example case 1. In the second case, at index 1, the sum of left side =1 is equal to the sum of the right side {50,-51,1,1}

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded