/-
You are given an array of non-negative integers, your task is to complete the series from 0 to the highest number in the array.

If the numbers in the sequence provided are not in order you should order them, but if a value repeats, then you must return a sequence with only one item, and the value of that item must be 0. like this:
```
inputs        outputs
[2,1]     ->  [0,1,2]
[1,4,4,6] ->  [0]
```
Notes: all numbers are positive integers.

This is set of example outputs based on the input sequence.
```
inputs        outputs
[0,1]   ->    [0,1]
[1,4,6] ->    [0,1,2,3,4,5,6]
[3,4,5] ->    [0,1,2,3,4,5]
[0,1,0] ->    [0]
```
-/

-- <vc-helpers>
-- </vc-helpers>

def complete_series (arr : List Nat) : List Nat := sorry

theorem complete_series_returns_list (arr : List Nat) :
  ∃ l, complete_series arr = l := by sorry

theorem complete_series_main_property (arr : List Nat) :
  (∃ x ∈ arr, ∃ y ∈ arr, x = y ∧ arr.indexOf x ≠ arr.indexOf y) →
  complete_series arr = [0] := by sorry

theorem complete_series_complete_sequence (arr : List Nat) :
  (∀ x ∈ arr, ∀ y ∈ arr, x = y → arr.indexOf x = arr.indexOf y) →
  let maxVal := arr.maximum?.getD 0
  complete_series arr = List.range (maxVal + 1) := by sorry 

theorem complete_series_length (arr : List Nat) :
  (∀ x ∈ arr, ∀ y ∈ arr, x = y → arr.indexOf x = arr.indexOf y) →
  let maxVal := arr.maximum?.getD 0
  (complete_series arr).length = maxVal + 1 := by sorry

theorem complete_series_contains_all_elements (arr : List Nat) : 
  (∀ x ∈ arr, ∀ y ∈ arr, x = y → arr.indexOf x = arr.indexOf y) →
  let maxVal := arr.maximum?.getD 0
  ∀ i, i ≤ maxVal → i ∈ complete_series arr := by sorry

theorem complete_series_monotone (arr : List Nat) :
  (∀ x ∈ arr, ∀ y ∈ arr, x = y → arr.indexOf x = arr.indexOf y) →
  ∀ i j, i < j → i < (complete_series arr).length → j < (complete_series arr).length →
  (complete_series arr).get ⟨i, by sorry⟩ ≤ (complete_series arr).get ⟨j, by sorry⟩ := by sorry

/-
info: [0, 1]
-/
-- #guard_msgs in
-- #eval complete_series [0, 1]

/-
info: [0, 1, 2, 3, 4, 5, 6]
-/
-- #guard_msgs in
-- #eval complete_series [1, 4, 6]

/-
info: [0]
-/
-- #guard_msgs in
-- #eval complete_series [1, 4, 4, 6]

-- Apps difficulty: introductory
-- Assurance level: unguarded