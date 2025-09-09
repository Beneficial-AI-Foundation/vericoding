-- <vc-helpers>
-- </vc-helpers>

def multiple_of_index (arr : List Int) : List Int :=
  sorry

theorem multiple_of_index_basic_properties (arr : List Int) (h : arr ≠ []) :
  let result := multiple_of_index arr
  -- Result length is at most one less than input length
  result.length ≤ arr.length - 1 ∧
  -- Every element in result appears in original array 
  ∀ x ∈ result, x ∈ arr :=
  sorry

theorem empty_result_divisibility (arr : List Int) (h : arr ≠ []) :
  let result := multiple_of_index arr
  (∀ (i : Fin arr.length), 1 ≤ i.val → (arr.get i) % i.val ≠ 0) →
  result = [] :=
  sorry

theorem all_zeros (arr : List Int) (h : arr.length ≥ 2) (h2 : ∀ x ∈ arr, x = 0) :
  let result := multiple_of_index arr
  (∀ x ∈ result, x = 0) ∧
  result.length = arr.length - 1 :=
  sorry

/-
info: [-6, 32, 25]
-/
-- #guard_msgs in
-- #eval multiple_of_index [22, -6, 32, 82, 9, 25]

/-
info: [-1, 10]
-/
-- #guard_msgs in
-- #eval multiple_of_index test2

/-
info: [-85, 72, 0, 68]
-/
-- #guard_msgs in
-- #eval multiple_of_index test3

-- Apps difficulty: introductory
-- Assurance level: unguarded