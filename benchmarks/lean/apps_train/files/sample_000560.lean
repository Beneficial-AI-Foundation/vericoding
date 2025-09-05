Chef found a strange string yesterday - a string of signs s, where each sign is either a '<', '=' or a '>'. Let N be the length of this string. Chef wants to insert N + 1 positive integers into this sequence and make it valid. A valid sequence is a sequence where every sign is preceded and followed by an integer, and the signs are correct. That is, if a sign '<' is preceded by the integer a and followed by an integer b, then a should be less than b. Likewise for the other two signs as well. 
Chef can take some positive integers in the range [1, P] and use a number in the range as many times as he wants.
Help Chef find the minimum possible P with which he can create a valid sequence.

-----Input-----
The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows.
The only line of each test case contains the string of signs s, where each sign is either '<', '=' or a '>'. 

-----Output-----
For each test case, output a single line containing an integer corresponding to the minimum possible P. 

-----Constraints-----
- 1 ≤ T, |s| ≤ 105
- 1 ≤ Sum of |s| over all test cases in a single test file ≤ 106

-----Subtasks-----
Subtask #1 (30 points)
- 1 ≤ T, |s| ≤ 103
- 1 ≤ Sum of |s| over all test cases in a single test file ≤ 104

Subtask #2 (70 points)
- Original constraints

-----Example-----
Input:
4
<<<
<><
<=>
<=<

Output:
4
2
2
3

-----Explanation-----
Here are some possible valid sequences which can be formed with the minimum P for each of the test cases:
1 < 2 < 3 < 4
1 < 2 > 1 < 2
1 < 2 = 2 > 1
1 < 2 = 2 < 3

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible