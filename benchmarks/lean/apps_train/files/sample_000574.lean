Chef has an array A consisting of N integers (1-based indexing). He asks you to perform the following operation M times:

	for i = 2 to N:
		Ai = Ai + Ai-1

Your task is to find the xth element of the array (i.e., Ax) after performing the above operation M times. As the answer could be large, please output it modulo 109 + 7.

-----Input-----
- The first line of input contains an integer T denoting the number of test cases.
- The first line of each test case contains three space-separated integers — N, x, and M — denoting the size of the array, index of the element you need to find, and the amount of times you need to repeat operation before finding the element, respectively. The second line contains N space-separated integers A1, A2, …, AN.

-----Output-----
For each test case, output a single line containing one integer: Ax modulo 109 + 7. 

-----Constraints-----
- 1 ≤ T ≤ 10
- 1 ≤ x ≤ N ≤ 105
- 1 ≤ M ≤ 1018 
- 1 ≤ Ai  ≤ 1018

-----Subtasks-----Subtask 1 (8 points):
- 1 ≤ x ≤ min{2, N}Subtask 2 (24 points):
- 1 ≤ N * M ≤ 106Subtask 3 (68 points):  No additional constraints

-----Example-----
Input:
2
3 2 3
1 2 3
3 3 3 
1 2 3

Output:
5
15

-----Explanation-----
Values in the array A:
- Before the operations: [1, 2, 3]
- After the first operation: [1, 3, 6]
- After the second operation: [1, 4, 10]
- After the third operation: [1, 5, 15]

Since input file can be fairly large (about 8 MB), it's recommended to use fast I/O (for example, in C++, use scanf/printf instead of cin/cout).

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
