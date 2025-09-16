-- <vc-preamble>
def select_subarray (arr : List Int) : Nat × Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_ratio (arr : List Int) (idx : Nat) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem select_subarray_index_bounds {arr : List Int}
  (h_size : arr.length ≥ 2)
  (h_nonzero : ∀ x ∈ arr, x ≠ 0) :
  (select_subarray arr).1 < arr.length := by
  sorry

theorem select_subarray_matches_input {arr : List Int}
  (h_size : arr.length ≥ 2) 
  (h_nonzero : ∀ x ∈ arr, x ≠ 0) :
  (select_subarray arr).2 = arr[(select_subarray arr).1]! := by
  sorry

theorem select_subarray_minimum_ratio {arr : List Int}
  (h_size : arr.length ≥ 2)
  (h_nonzero : ∀ x ∈ arr, x ≠ 0) :
  ∀ i < arr.length,
    get_ratio arr (select_subarray arr).1 ≤ get_ratio arr i := by
  sorry

/-
info: [3, -8]
-/
-- #guard_msgs in
-- #eval select_subarray [1, 23, 2, -8, 5]

/-
info: [2, 23]
-/
-- #guard_msgs in
-- #eval select_subarray [1, 3, 23, 4, 2, -8, 5, 18]

/-
info: [[3, 100], [4, 200]]
-/
-- #guard_msgs in
-- #eval select_subarray [10, 20, -30, 100, 200]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded