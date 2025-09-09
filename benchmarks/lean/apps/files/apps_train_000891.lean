/-
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
-/

def solve_min_pairs (n : Nat) (k : Int) (arr : List Int) : Int × Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def count_pairs_with_diff (arr : List Int) (k : Int) (min_diff : Int) : Nat :=
  sorry

theorem solve_min_pairs_nonneg_diff (n : Nat) (k : Int) (arr : List Int)
  (h1: n ≥ 2) (h2: arr.length = n) :
  let (min_diff, _) := solve_min_pairs n k arr
  min_diff ≥ 0 := by
  sorry

theorem solve_min_pairs_positive_count (n : Nat) (k : Int) (arr : List Int) 
  (h1: n ≥ 2) (h2: arr.length = n) :
  let (_, count) := solve_min_pairs n k arr
  count > 0 := by
  sorry

theorem solve_min_pairs_count_accurate (n : Nat) (k : Int) (arr : List Int)
  (h1: n ≥ 2) (h2: arr.length = n) :
  let (min_diff, count) := solve_min_pairs n k arr
  count_pairs_with_diff arr k min_diff = count := by
  sorry

theorem solve_min_pairs_minimal (n : Nat) (k : Int) (arr : List Int)
  (h1: n ≥ 2) (h2: arr.length = n) :
  let (min_diff, _) := solve_min_pairs n k arr
  ∀ i j, 0 ≤ i ∧ i < n ∧ j > i ∧ j < n →
    let diff := arr[i]! + arr[j]! - k
    if diff ≥ 0 then diff ≥ min_diff else -diff ≥ min_diff := by
  sorry

theorem solve_min_pairs_permutation_invariant (n : Nat) (k : Int) (arr1 arr2 : List Int)
  (h1: n ≥ 2) (h2: arr1.length = n) (h3: arr2.length = n) 
  (h4: arr2.Perm arr1) :
  solve_min_pairs n k arr1 = solve_min_pairs n k arr2 := by
  sorry

/-
info: (1, 4)
-/
-- #guard_msgs in
-- #eval solve_min_pairs 4 9 [4, 4, 2, 6]

/-
info: (2, 1)
-/
-- #guard_msgs in
-- #eval solve_min_pairs 2 10 [3, 5]

/-
info: (4, 3)
-/
-- #guard_msgs in
-- #eval solve_min_pairs 3 12 [4, 4, 4]

-- Apps difficulty: interview
-- Assurance level: unguarded