You are given an array of N integers a1, a2, ..., aN and an integer K. Find the number of such unordered pairs {i, j} that 

- i ≠ j
- |ai + aj - K| is minimal possible

Output  the minimal possible value of |ai + aj - K| (where i ≠ j) and the number of such pairs for the given array and the integer K.

-----Input-----
The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows.

The first line of each test case consists of two space separated integers - N and K respectively.

The second line contains N single space separated integers - a1, a2, ..., aN respectively.

-----Output-----
For each test case, output a single line containing two single space separated integers - the minimal possible value of |ai + aj - K| and the number of unordered pairs {i, j} for which this minimal difference is reached.

-----Constraints-----

- 1 ≤ T ≤ 50
- 1 ≤ ai, K ≤ 109
- N = 2 - 31 point.
- 2 ≤ N ≤ 1000 - 69 points.

-----Example-----
Input:
1   
4 9
4 4 2 6

Output:
1 4

-----Explanation:-----
The minimal possible absolute difference of 1 can be obtained by taking the pairs of a1 and a2, a1 and a4, a2 and a4, a3 and a4.

def solve_min_pairs (n : Nat) (k : Int) (arr : List Int) : Int × Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded