/-
The chef has one array of N natural numbers (might be in sorted order). Cheffina challenges chef to find the total number of inversions in the array.

-----Input:-----
- First-line will contain $T$, the number of test cases. Then the test cases follow. 
- Each test case contains two lines of input, $N$.
- N space-separated natural numbers. 

-----Output:-----
For each test case, output in a single line answer as the total number of inversions.

-----Constraints-----
- $1 \leq T \leq 10$
- $1 \leq N \leq 10^5$
- $1 \leq arr[i] \leq 10^5$

-----Sample Input:-----
1
5
5 4 1 3 2

-----Sample Output:-----
8
-/

-- <vc-helpers>
-- </vc-helpers>

def countInversions (arr : List Int) : Nat := sorry

theorem empty_or_single_zero {arr : List Int} :
  arr.length ≤ 1 → countInversions arr = 0 := sorry

theorem sorted_zero {arr : List Int} (h : Sorted Int arr (. ≤ .)) :
  countInversions arr = 0 := sorry

theorem count_nonnegative {arr : List Int} :
  countInversions arr ≥ 0 := sorry

theorem count_bounded {arr : List Int} :
  countInversions arr ≤ (arr.length * (arr.length - 1)) / 2 := sorry

theorem increasing_zero {arr : List Int} (h : Sorted Int arr (. < .)) :
  countInversions arr = 0 := sorry

theorem decreasing_triangular {arr : List Int} (h : Sorted Int arr (fun x y => y < x)) :
  let n := arr.length - 1
  countInversions arr = (n * (n + 1)) / 2 := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval count_inversions [5, 4, 1, 3, 2]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_inversions [1, 2, 3, 4, 5]

/-
info: 10
-/
-- #guard_msgs in
-- #eval count_inversions [5, 4, 3, 2, 1]

-- Apps difficulty: interview
-- Assurance level: unguarded