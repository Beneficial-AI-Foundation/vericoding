For a permutation P = (p1, p2, ..., pN) of numbers [1, 2, ..., N], we define the function f(P) = max(p1, p2) + max(p2, p3) + ... + max(pN-1, pN).
You are given N and an integer K. Find and report a permutation P of [1, 2, ..., N] such that f(P) = K, if such a permutation exists.
Note f([1]) = 0.

-----Input-----
- The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows.
- The only line of each test case consists of two space-separated integers N, K respectively.

-----Output-----
For each test case, if a permutation satisfying the condition exists, output a single line containing N space-separated integers which denotes any such permutation. If no such permutation exists, output a single integer -1 instead.
Use fast I/O methods since the size of the output is large.

-----Constraints-----
- 1 ≤ T ≤ 40
- 1 ≤ N ≤ 105
- Sum of N over all test cases in each file ≤ 106
- 0 ≤ K ≤ 2 * 1010

-----Example-----
Input:
3
4 12
2 2
5 14

Output:
-1
1 2
5 4 3 2 1

-----Explanation-----
Example 1. There doesn't exist any permutation of numbers [1, 2, 3, 4] that can have its f value equal to 4. Hence answer is -1.
Example 2. The permutations [1, 2] and [2, 1] both have their f values equal to 2. You can print any of these two permutations. 
Example 3. The permutation [5, 4, 3, 2, 1]
has f value = max(5, 4) + max(4, 3) + max(3, 2) + max(2, 1) = 5 + 4 + 3 + 2 = 14.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
