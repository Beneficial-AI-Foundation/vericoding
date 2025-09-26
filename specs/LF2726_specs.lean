-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def merge_arrays (a b : List Int) : List Int := sorry

theorem merge_arrays_sorted_property
  (a b : List Int) :
  let result := merge_arrays a b
  ∀ i j, i < j → j < result.length → result[i]! ≤ result[j]! := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem merge_arrays_elements_from_inputs
  (a b : List Int) (x : Int) :
  x ∈ merge_arrays a b →
  x ∈ a ∨ x ∈ b := sorry

theorem merge_arrays_no_duplicates
  (a b : List Int) :
  let result := merge_arrays a b
  ∀ x ∈ result, ∀ y ∈ result, x = y → result.indexOf x = result.indexOf y := sorry

theorem merge_arrays_different_counts_excluded
  (a b : List Int) (x : Int) :
  x ∈ a ∧ x ∈ b →
  (List.countP (· = x) a ≠ List.countP (· = x) b) →
  x ∉ merge_arrays a b := sorry

theorem merge_arrays_unique_elements_included
  (a b : List Int) (x : Int) :
  (x ∈ a ∧ x ∉ b) ∨ (x ∉ a ∧ x ∈ b) →
  x ∈ merge_arrays a b := sorry

theorem merge_arrays_same_count_included
  (a b : List Int) (x : Int) :
  x ∈ a ∧ x ∈ b →
  List.countP (· = x) a = List.countP (· = x) b →
  x ∈ merge_arrays a b := sorry

theorem merge_arrays_idempotent
  (a : List Int) :
  let result := merge_arrays a a
  ∀ x, x ∈ result ↔ x ∈ a := sorry

theorem merge_arrays_symmetric
  (a b : List Int) :
  merge_arrays a b = merge_arrays b a := sorry

/-
info: [15, 20, 25, 27, 30, 7000, 7200]
-/
-- #guard_msgs in
-- #eval merge_arrays [10, 10, 10, 15, 20, 20, 25, 25, 30, 7000] [10, 15, 20, 20, 27, 7200]

/-
info: [2, 3, 500, 550, 1000, 1400, 1500, 3500]
-/
-- #guard_msgs in
-- #eval merge_arrays [500, 550, 1000, 1000, 1400, 3500] [2, 2, 2, 2, 3, 1500]

/-
info: [7]
-/
-- #guard_msgs in
-- #eval merge_arrays [5] [5, 5, 7]
-- </vc-theorems>