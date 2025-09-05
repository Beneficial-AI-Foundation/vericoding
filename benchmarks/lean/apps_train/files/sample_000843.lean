Given N, count how many permutations of [1, 2, 3, ..., N] satisfy the following property.

Let P1, P2, ..., PN denote the permutation. The property we want to satisfy is that there exists an i between 2 and n-1 (inclusive) such that

- Pj > Pj + 1  ∀    i ≤ j ≤ N - 1.
- Pj > Pj - 1  ∀    2 ≤ j ≤ i.

-----Input-----
First line contains T, the number of test cases. Each test case consists of N in one line.

-----Output-----
For each test case, output the answer modulo 109+7.

-----Constraints-----
- 1 ≤ T ≤ 100
- 1 ≤ N ≤ 109

-----Subtasks-----
- Subtask #1(40 points): 1 ≤ N ≤ 1000
- Subtask #2(60 points): original constraints

-----Example-----
Input:
2
2
3

Output:
0
2

-----Explanation-----

Test case 1:

No permutation satisfies.

Test case 2:

Permutations [1, 3, 2] and [2, 3, 1] satisfy the property.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
