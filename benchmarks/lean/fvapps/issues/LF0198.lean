-- <vc-preamble>
def longestMountain (arr : Array Int) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSorted (arr : Array Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mountain_length_min_or_zero {arr : Array Int} :
  let result := longestMountain arr
  result = 0 ∨ result ≥ 3
  := sorry

theorem mountain_length_bounded {arr : Array Int} :
  longestMountain arr ≤ arr.size
  := sorry

theorem flat_sequence_no_mountain {arr : Array Int} :
  let doubled := arr.concatMap (fun x => #[x, x]) 
  longestMountain doubled = 0
  := sorry

theorem single_element_no_mountain {x : Int} :
  longestMountain #[x] = 0
  := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval longestMountain #[2, 1, 4, 7, 3, 2, 5]

/-
info: 0
-/
-- #guard_msgs in
-- #eval longestMountain #[2, 2, 2]

/-
info: 9
-/
-- #guard_msgs in
-- #eval longestMountain #[1, 2, 3, 4, 5, 4, 3, 2, 1]
-- </vc-theorems>