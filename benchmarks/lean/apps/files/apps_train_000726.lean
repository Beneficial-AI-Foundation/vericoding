-- <vc-preamble>
def min_temple_operations (n : Nat) (heights : List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_sum : List Nat → Nat 
  | [] => 0
  | (h :: t) => h + list_sum t
-- </vc-definitions>

-- <vc-theorems>
theorem min_temple_operations_nonnegative (n : Nat) (heights : List Nat) :
  heights.length = n →
  min_temple_operations n heights ≥ 0 :=
sorry

theorem min_temple_operations_preserves_input (n : Nat) (heights : List Nat) :
  heights.length = n →
  heights = heights :=
sorry

theorem min_temple_operations_bounded_by_sum (n : Nat) (heights : List Nat) :
  heights.length = n →
  min_temple_operations n heights ≤ list_sum heights :=
sorry

theorem min_temple_operations_perfect (heights : List Nat) :
  heights = [1,2,3,2,1] →
  min_temple_operations 5 heights = 0 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_temple_operations 3 [1, 2, 1]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_temple_operations 4 [1, 1, 2, 1]

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_temple_operations 5 [1, 2, 6, 2, 1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded