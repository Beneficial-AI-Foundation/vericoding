/-
You are given an array A, consisting of N integers and an array B, consisting of M integers.
The subsequence of A is the array that can be obtained by picking the elements at the arbitrary sorted set of positions from A.
Your task is to count the number of such subsequences C of A that:

- C contains exactly M elements.
- The array (C+B) is non-decreasing. Here by + operation, we mean element-wise sum. 

For example, the array (4, 8, 5) plus the array (10, 20, 30) is (14, 28, 35).

Formally, (C+B) is an array of size M such that (C+B)i = Ci + Bi.

In case some subsequence appears more that once, you should counts it as many times as it appears.

Formally, two subarrays of an array a, (ai_1, ai_2, ... ,ai_n) and (aj_1, aj_2, ... ,aj_m) will be considered different if either their lengths are different i.e. n != m or there exists an index k such that such that i_k  != j_k.

Since the answer can be very large, we ask you to calculate it, modulo 109+7.

-----Input-----
The first line of input contains a pair of space separated integers N and M, denoting the number of elements in the array A and the number of elements in the array B.
The second line contains N space-separated integers Ai, denoting the array A.
The third line contains M space-separated integers Bj, denoting the array B.

-----Output-----
Output a single line containing the number of subsequences C as asked in the problem, modulo 109+7.

-----Constraints-----
- 1 ≤ Ai, Bi ≤ 109
- 1 ≤ M ≤ N

-----Subtasks-----
- Subtask #1 (33 points): 1 ≤ N ≤ 50, 1 ≤ M ≤ 5
- Subtask #2 (33 points): 1 ≤ N ≤ 500, 1 ≤ M ≤ 50
- Subtask #3 (34 points): 1 ≤ N ≤ 2000, 1 ≤ M ≤ 1000

-----Example-----
Input #1:
5 3
1 5 2 4 7
7 9 6

Output #1:
4

Input #2:
4 2
7 7 7 7
3 4

Output #2:
6

-----Explanation-----
Example case 1. The suitable subsequences are (1, 2, 7), (1, 4, 7), (5, 4, 7), (2, 4, 7).
Example case 2. The suitable subsequence is (7, 7), and it appears 6 times:

- at indices (1, 2)
- at indices (1, 3)
- at indices (1, 4)
- at indices (2, 3)
- at indices (2, 4)
- at indices (3, 4)

So, the answer is 6.
-/

-- <vc-helpers>
-- </vc-helpers>

def count_valid_subsequences (n m : Nat) (a b : List Nat) : Nat := sorry

theorem count_valid_subsequences_nonnegative 
  (n m : Nat) (a b : List Nat) : 
  count_valid_subsequences n m a b ≥ 0 := sorry

theorem count_valid_subsequences_modulo_bound
  (n m : Nat) (a b : List Nat) :
  count_valid_subsequences n m a b < (10^9 + 7) := sorry

theorem increasing_arrays_valid
  (n m : Nat) (h1 : n > 0) (h2 : m > 0) (h3 : n ≤ 5) (h4 : m ≤ 5) :
  count_valid_subsequences n m (List.range' 1 n) (List.range' 1 m) ≥ 0 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_valid_subsequences 5 3 [1, 5, 2, 4, 7] [7, 9, 6]

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_valid_subsequences 4 2 [7, 7, 7, 7] [3, 4]

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible