-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countInversions (arr : List Int) : Nat := sorry

theorem empty_or_single_zero {arr : List Int} :
  arr.length ≤ 1 → countInversions arr = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>