Chef recently learned about concept of periodicity of strings. A string is said to have a period P, if P divides N and for each i, the i-th of character of the string is same as i-Pth character (provided it exists), e.g. "abab" has a period P = 2, It also has a period of P = 4, but it doesn't have a period of 1 or 3.
Chef wants to construct a string of length N that is a palindrome and has a period P. It's guaranteed that N is divisible by P. This string can only contain character 'a' or 'b'. Chef doesn't like the strings that contain all a's or all b's.
Given the values of N, P, can you construct one such palindromic string that Chef likes? If it's impossible to do so, output "impossible" (without quotes)

-----Input-----
The first line of the input contains an integer T denoting the number of test cases.
The only line of each test case contains two space separated integers N, P.

-----Output-----
For each test case, output a single line containing the answer of the problem, i.e. the valid string if it exists otherwise "impossible"  (without quotes). If there are more than possible answers, you can output any.

-----Constraints-----
- 1 ≤ T ≤ 20
- 1 ≤ P, N ≤ 105

-----Subtasks-----
- Subtask #1 (25 points) : P = N
- Subtask #2 (75 points) : No additional constraints

-----Example-----
Input
5
3 1
2 2
3 3
4 4
6 3

Output
impossible
impossible
aba
abba
abaaba

-----Explanation-----
Example 1: The only strings possible are either aaa or bbb, which Chef doesn't like. So, the answer is impossible.
Example 2: There are four possible strings, aa, ab, ba, bb. Only aa and bb are palindromic, but Chef doesn't like these strings. Hence, the answer is impossible.
Example 4: The string abba is a palindrome and has a period of 4.
Example 5: The string abaaba is a palindrome and has a period of length 3.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded