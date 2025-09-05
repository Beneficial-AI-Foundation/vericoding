Chef has an array A consisting of N elements. He wants to find number of pairs of non-intersecting segments [a, b] and [c, d] (1 ≤ a ≤ b < c ≤ d ≤ N) such there is no number that occurs in the subarray {Aa, Aa+1, ... , Ab} and   {Ac, Ac+1, ... , Ad} simultaneously. 
Help Chef to find this number.

-----Input-----
- The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows.
- The first line of each test case contains a single integer N denoting the number of elements in the array.
- The second line contains N space-separated integers A1, A2, ..., AN. 

-----Output-----
- For each test case, output a single line containing one integer - number of pairs of non-intersecting segments. 

-----Constraints-----
- 1 ≤ T ≤ 5
- 1 ≤ N ≤ 1000
- 1 ≤ Ai ≤ 109

-----Subtasks-----Subtask 1 (7 points)
- 1 ≤ N ≤ 20Subtask 2 (34 points)
- 1 ≤ N ≤ 300Subtask 3 (59 points)
- Original constraints

-----Example-----
Input:
2
3
1 2 3
4
1 2 1 2

Output:
5
4

-----Explanation-----
Example case 1.
All possible variants are correct: {[1, 1], [2, 2]}, {[1, 1], [2, 3]}, {[1, 2], [3, 3]}, {[2, 2], [3, 3]}, {[1,1], [3, 3]}.

Example case 2.
Correct segments: {[1, 1], [2, 2]}, {[1, 1], [4, 4]}, {[2, 2], [3, 3]}, {[3, 3], [4, 4]}.

def Segment := List Int
def SegmentList := List Segment

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded