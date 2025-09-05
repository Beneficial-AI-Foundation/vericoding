There are N hills in a row numbered 1 through N from left to right. Each hill has a height; for each valid i, the height of the i-th hill is Hi. Chef is initially on the leftmost hill (hill number 1). He can make an arbitrary number of jumps (including zero) as long as the following conditions are satisfied:

- Chef can only jump from each hill to the next hill, i.e. from the i-th hill, he can jump to the i+1-th hill (if it exists).
- It's always possible to jump to a hill with the same height as the current hill.
- It's possible to jump to a taller hill if it's higher than the current hill by no more than U.
- It's possible to jump to a lower hill if it's lower than the current hill by no more than D.
- Chef can use a parachute and jump to a lower hill regardless of its height (as long as it's lower than the current hill). This jump can only be performed at most once.

Chef would like to move as far right as possible. Determine the index of the rightmost hill Chef can reach.

-----Input-----
- The first line of the input contains a single integer T denoting the number of test cases. The description of T test cases follows.
- The first line of each test case contains three space-separated integers N, U and D.
- The second line contains N space-separated integers H1, H2, ..., HN.

-----Output-----
For each test case, print a single line containing one integer — the index of the rightmost reachable hill.

-----Constraints-----
- 1 ≤ T ≤ 100
- 1 ≤ N ≤ 100
- 1 ≤ U, D ≤ 1,000,000
- 1 ≤ Hi ≤ 1,000,000 for each valid i

-----Subtasks-----
Subtask #1 (100 points): original constraints

-----Example-----
Input:

3
5 3 2
2 5 2 6 3
5 2 3
4 4 4 4 4
5 2 7
1 4 3 2 1

Output:

3
5
1

-----Explanation-----
Example case 1: Chef can jump to second hill because it's higher by no more than U=3 than first hill, to jump to third hill Chef has to use parachute 
because it's lower than second hill by 3 which is more than D=2, Chef can't jump to fourth hill because it's higher than third hill by 4 which is more than U=3
Example case 2: All hills are of the same height, so chef can reach the last hill with no problems.
Example case 3: Chef can't jump to second hill because it's too high for him

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded