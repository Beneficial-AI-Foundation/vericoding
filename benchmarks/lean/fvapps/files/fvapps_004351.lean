-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def merge_arrays (arr1 : List Int) (arr2 : List Int) : List Int := sorry

theorem merge_arrays_ordered (arr1 arr2 : List Int) :
  ∀ i j, i < j → i < (merge_arrays arr1 arr2).length → j < (merge_arrays arr1 arr2).length →
  (merge_arrays arr1 arr2)[i]! ≤ (merge_arrays arr1 arr2)[j]! := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem merge_arrays_unique (arr1 arr2 : List Int) :
  ∀ i j, i < (merge_arrays arr1 arr2).length → j < (merge_arrays arr1 arr2).length →
  i ≠ j → (merge_arrays arr1 arr2)[i]! ≠ (merge_arrays arr1 arr2)[j]! := sorry

theorem merge_arrays_contains_inputs (arr1 arr2 : List Int) :
  (∀ x ∈ arr1, x ∈ merge_arrays arr1 arr2) ∧ 
  (∀ x ∈ arr2, x ∈ merge_arrays arr1 arr2) := sorry

theorem merge_arrays_no_extra_elements (arr1 arr2 : List Int) :
  ∀ x ∈ merge_arrays arr1 arr2, x ∈ arr1 ∨ x ∈ arr2 := sorry

theorem merge_array_with_itself (arr : List Int) (x : Int) :
  x ∈ merge_arrays arr arr ↔ x ∈ arr := sorry

theorem merge_with_empty_left (arr : List Int) :
  merge_arrays arr [] = merge_arrays arr arr := sorry

theorem merge_with_empty_right (arr : List Int) :
  merge_arrays [] arr = merge_arrays arr arr := sorry
-- </vc-theorems>