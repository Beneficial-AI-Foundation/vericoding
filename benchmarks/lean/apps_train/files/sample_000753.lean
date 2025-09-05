You are given a binary string S of N bits. The bits in the string are indexed starting from 1. S[i] denotes the ith bit of S.

Let's say that a sequence i1, i2, …, iK(1 ≤ K; 1 ≤ i1 < i2 < … < iK ≤ N) produces a palindrome when applied to S, if the string S[i1] S[i2] … S[ik] is a palindrome (that is, reads the same backward or forward).

In addition, a sequence i1, i2, …, iK(1 ≤ K; 1 ≤ i1 < i2 < … < iK ≤ N) is said to be exponential, if ij + 1 = p * ij for each integer 1 ≤ j < K and for some integer p > 1. Note, that a sequence of one element is always exponential.

Your task is to count the number of exponential sequences that produce a palindrome when applied to S.

-----Input-----
The first line of input contains an integer T denoting the number of test cases. The description of T test cases follows.

The only line of description for each test case contains a binary string S of N bits.

-----Output-----

For each test case, output a single line containing the number of exponential sequences that produce a palindrome.

-----Constraints-----
- 1 ≤ T ≤ 10
- Subtask 1(20 points): 1 ≤ N ≤ 20
- Subtask 2(30 points): 1 ≤ N ≤ 1000
- Subtask 3(50 points): 1 ≤ N ≤ 5 × 105

-----Note-----

The first test of the first subtask is the example test. It's made for you to make sure that your solution produces the same verdict both on your machine and our server.

-----Time Limits-----

Time limit for the first and the second subtasks is 3s. Time limit for the third subtask is 6s.

-----Example-----
Input:
2
11010
101001011

Output:
9
18

-----Explanation of the first case in the example test-----

The following sequences are counted in the answer: {1}, {2}, {3}, {4}, {5}, {1, 2}, {1, 4}, {2, 4}, {1, 2, 4}.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
