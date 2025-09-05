You are given a sequence of n integers a1, a2, ..., an and an integer d.
Find the length of the shortest non-empty contiguous subsequence with sum of elements at least d. Formally, you should find the smallest positive integer k with the following property: there is an integer s (1 ≤ s ≤ N-k+1) such that as + as+1 + ... + as+k-1 ≥ d.

-----Input-----

- The first line of the input contains a single integer T denoting the number of test cases. The description of T test cases follows.
- The first line of each test case contains two space-separated integers n and d.
- The second line contains n space-separated integers a1, a2, ..., an.

-----Output-----
For each test case, print a single line containing one integer — the length of the shortest contiguous subsequence with sum of elements ≥ d. If there is no such subsequence, print -1 instead.

-----Constraints-----
- 1 ≤ T ≤ 105
- 1 ≤ n ≤ 105
- -109 ≤ d ≤ 109
- -104 ≤ ai ≤ 104
- 1 ≤ sum of n over all test cases ≤ 2 · 105

-----Example-----
Input:

2
5 5
1 2 3 1 -5
5 1
1 2 3 1 -5

Output:

2
1

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
