-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bad_apples (apples : List (Nat × Nat)) : List (List Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bad_apples_output_structure (apples : List (Nat × Nat)) :
  let result := bad_apples apples
  -- Output is list of lists with exactly 2 elements
  ∀ sublist ∈ result, sublist.length = 2 := by
  sorry

theorem bad_apples_no_zeros (apples : List (Nat × Nat)) :
  let result := bad_apples apples
  -- No zeros in output lists
  ∀ sublist ∈ result, ∀ x ∈ sublist, x ≠ 0 := by
  sorry

theorem bad_apples_values_subset (apples : List (Nat × Nat)) :
  let result := bad_apples apples
  let input_values := (apples.map (fun p => [p.1, p.2])).join.filter (fun n => n ≠ 0)
  -- Output values come from input
  ∀ sublist ∈ result, ∀ x ∈ sublist, x ∈ input_values := by
  sorry

theorem bad_apples_length (apples : List (Nat × Nat)) :
  let result := bad_apples apples
  -- Output no longer than input
  result.length ≤ apples.length := by
  sorry

theorem bad_apples_all_zeros (apples : List (Nat × Nat)) :
  (∀ p ∈ apples, p.1 = 0 ∧ p.2 = 0) →
  -- All zero pairs give empty result  
  bad_apples apples = [] := by
  sorry

theorem bad_apples_value_counts (apples : List (Nat × Nat)) (x : Nat) :
  let result := bad_apples apples
  -- Output value counts don't exceed input counts
  x ≠ 0 →
  let input_count := (apples.map (fun p => [p.1, p.2])).join.filter (fun n => n = x) |>.length
  let output_count := result.join.filter (fun n => n = x) |>.length
  output_count ≤ input_count := by
  sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval bad_apples []

/-
info: expected
-/
-- #guard_msgs in
-- #eval bad_apples [[1, 3], [7, 6], [7, 2], [1, 3], [0, 2], [4, 5], [0, 3], [7, 6]]

/-
info: []
-/
-- #guard_msgs in
-- #eval bad_apples [[0, 0], [0, 0]]
-- </vc-theorems>