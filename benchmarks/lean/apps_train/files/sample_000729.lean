	Chef has a cubic die with 6 faces kept on an infinite plane. Each face has a distinct integer in the range [1,6] written on it, but the exact arrangement of the numbers on the faces of the die is unknown to Chef. Curiosity gets the better of Chef and he wants to find out o(1), o(2), ..., o(6), where o(i) is the number written opposite to the number i.

	Chef performs the following N-1 steps to learn the exact arrangement of the numbers on the die. In the i-th step, Chef pushes the die in some direction (there are 4 possible directions), and the die rolls 90o in this direction. The picture below demonstrates a die and the result that it produced after rolling in each of the 4 directions respectively. For this die, we have o(1)=4, o(2)=5, o(3)=6, o(4)=1, o(5)=2, o(6)=3.

	Chef records N numbers A1, A2, ..., AN, where Ai is the number written on the top of the die before the i-th step. However, the information on the direction in which he pushes the die each time are lost. Can you help him determine the arrangement of 1-6? You need to output o(1), o(2), ..., o(6). If there are multiple solutions, output any one of them.

-----
	Input-----
- The first line of input contains a single integer T, the number of test cases.
- Each test case consists of two lines.
- The first line contains an integer N, and the second line contains N space-separated integers A1, A2, ..., AN.

-----
	Output-----

	For each test case, output one line. If a possible solution exists, then output 6 space-separated integers o(1), o(2), ..., o(6); otherwise, output -1.

-----
	Constraints-----

- 1 ≤ T, N ≤ 500
- 1 ≤ Ai ≤ 6

	Subtask #1 (17 points):

- N ≤ 2

	Subtask #2 (83 points):

- original constraints

-----
	Example-----
Input:
4
9
1 3 4 6 1 3 4 6 1
10
1 2 1 3 1 4 1 5 1 6
6
1 2 3 4 5 6
4
1 3 3 1

Output:
2 1 6 5 4 3
-1
4 5 6 1 2 3
-1

-----
	Explanation-----
Example case 1: See below.

Example case 2: You can prove that there's no solution.
Example case 3: The solution is not unique. 3 5 1 6 2 4 is another valid solution.

def solveDie (n : Nat) (nums : List Nat) : List Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
