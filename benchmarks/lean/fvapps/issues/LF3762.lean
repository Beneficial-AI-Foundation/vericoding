-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rank_of_element (arr : List Int) (i : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rank_within_bounds {arr : List Int} {i : Nat} (h : i < arr.length) :
  let rank := rank_of_element arr i
  0 ≤ rank ∧ rank ≤ arr.length :=
sorry

theorem rank_exceeds_strictly_less {arr : List Int} {i : Nat} (h : i < arr.length) :
  let rank := rank_of_element arr i
  let target := arr[i]
  let strictly_less := (List.enum arr).filter (fun p => p.2 < target ∧ p.1 ≠ i) |>.length
  rank ≥ strictly_less :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval rank_of_element [2, 1, 2, 1, 2] 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval rank_of_element [2, 1, 2, 2, 2] 2

/-
info: 1
-/
-- #guard_msgs in
-- #eval rank_of_element [3, 2, 3, 4, 1] 1
-- </vc-theorems>