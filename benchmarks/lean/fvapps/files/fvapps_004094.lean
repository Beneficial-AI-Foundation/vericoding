-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hot_singles {α} [BEq α] (arr1 : List α) (arr2 : List α) : List α := sorry

theorem hot_singles_elements_from_inputs {α} [BEq α] (arr1 arr2 : List α) :
  ∀ x ∈ hot_singles arr1 arr2, x ∈ arr1 ∨ x ∈ arr2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hot_singles_exclusive {α} [BEq α] (arr1 arr2 : List α) :
  ∀ x ∈ hot_singles arr1 arr2, (x ∈ arr1) ≠ (x ∈ arr2) := sorry

theorem hot_singles_no_duplicates {α} [BEq α] (arr1 arr2 : List α) :
  List.Nodup (hot_singles arr1 arr2) := sorry

theorem hot_singles_symmetric_difference {α} [BEq α] (arr1 arr2 : List α) :
  ∀ x, x ∈ hot_singles arr1 arr2 ↔ (x ∈ arr1 ∧ x ∉ arr2) ∨ (x ∈ arr2 ∧ x ∉ arr1) := sorry

theorem hot_singles_empty_second {α} [BEq α] (arr : List α) :
  hot_singles arr [] = arr := sorry

theorem hot_singles_same_array {α} [BEq α] (arr : List α) :
  hot_singles arr arr = [] := sorry
-- </vc-theorems>