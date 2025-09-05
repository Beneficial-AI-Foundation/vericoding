Chef's loves his dog so much! Once his dog created two strings a and b each of length n consisting of digits 1 and 2, and even a problem about them!
Chef's Dog will tell by barking if a string x (also containing only digits 1 and 2 and with length N) is good or not by performing the following actions.

- It starts at first digit of the string, i.e. at i = 1. 
- It can move from digit i to either i - 1 or i + 1 if xi equals 1 and the corresponding digits exist. 
- It can move from digit i to either i - 2 or i + 2 if xi equals 2 and the corresponding digits exist. 
- It must visit each digit exactly once. 
- It must finish at the last digit (XN). 

Chef's dog wants to make both the strings a and b good by choosing some subset S (possibly empty) of indices of set {1, 2, ..., n} and swapping each index i ϵ S between string a and b, i.e. swapping ai and bi. Can you find how many such subsets S exist out there? As the answer could be large, output it modulo 109 + 7.

-----Input-----
The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows.
The first line contains string a.
The second line contains string b.

-----Output-----
For each test case, output a single line containing answer of the problem.

-----Constraints-----
- 1 ≤ T ≤ 20
- 1 ≤ |a| = |b| ≤ 105
- '1' ≤ ai, bi ≤ '2'

-----Subtasks-----
- Subtask #1 (30 points) |a|, |b| ≤  10
- Subtask #2 (70 points) original constraints

-----Example-----
Input:
2
1111
2211
222
111

Output:
8
0

-----Explanation-----
Test case 1.
Possible subsets are: 
{}, {1, 2}, {1, 2, 3}, {1, 2, 4}, {1, 2, 3, 4}, {3}, {4}, {3, 4}.

Test case 2. There are no possible sets S which can make both the strings good.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
