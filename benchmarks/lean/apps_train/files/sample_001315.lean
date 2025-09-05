A squarer is a simple and convenient device. You give it some positive integer X and it calculates its square.
Leha is implementing a module of this device which is responsible for squaring the numbers consisting of multiple repetitions of one digit. But it turned out that it's not as simple as he thought.
Please help him now!

-----Input-----
The first line contains one integer T denoting the number of testcases. The descriptions of T test cases follow.
Each of the following T lines contain 2 space-separated integers - N and D, respectively. It means that the number X in the corresponding testcase consists of the digit D repeated N times (in decimal representation).

-----Output-----
As the answer can be very large, we ask you to output its hash which is computed in the following way:
Let's consider the integer answer Y as a 0-indexed array starting from its leftmost digit. The hash function is calculated as:
p0*Y[0] + p1*Y[1] + ... + pM-1*Y[M-1] modulo 109 + 7 
where M is the length of the array representation of Y and p equals 23.

-----Constraints-----
- 1 ≤ T ≤ 20
- 1 ≤ D ≤ 9
- Subtask 1 (16 points): 1 ≤ N ≤ 9
- Subtask 2 (25 points): 1 ≤ N ≤ 100
- Subtask 3 (27 points): 1 ≤ N ≤ 2 × 104
- Subtask 4 (32 points): 1 ≤ N ≤ 106

-----Example-----
Input:3
1 4
3 6
3 5

Output:139
40079781
32745632

-----Explanation-----
In the first test case, X = 4 and Y = 16. Its hash equals 1*1 + 23*6 = 139.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible