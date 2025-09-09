/-
Given an array, find the duplicates in that array, and return a new array of those duplicates. The elements of the returned array should appear in the order when they first appeared as duplicates.

__*Note*__: numbers and their corresponding string representations should not be treated as duplicates (i.e., `"1" != 1`).

## Examples
```
[1, 2, 4, 4, 3, 3, 1, 5, 3, "5"]  ==>  [4, 3, 1]
[0, 1, 2, 3, 4, 5]                ==>  []
```
-/

-- <vc-helpers>
-- </vc-helpers>

def duplicates {α : Type u} [BEq α] (arr : List α) : List α := sorry

theorem duplicates_contains_only_duplicated_elements {α : Type u} [BEq α] (arr : List α) :
  ∀ x ∈ duplicates arr, (arr.count x) ≥ 2 := sorry

theorem duplicates_contains_all_duplicated_elements {α : Type u} [BEq α] (arr : List α) :
  ∀ x, (arr.count x) ≥ 2 → x ∈ duplicates arr := sorry

theorem duplicates_result_has_no_duplicates {α : Type u} [BEq α] (arr : List α) :
  ∀ x ∈ duplicates arr, (duplicates arr).count x = 1 := sorry

theorem duplicates_empty_for_unique {α : Type u} [BEq α] (arr : List α) :
  (∀ x ∈ arr, arr.count x = 1) → duplicates arr = [] := sorry

/-
info: [4, 3, 1]
-/
-- #guard_msgs in
-- #eval duplicates [1, 2, 4, 4, 3, 3, 1, 5, 3, "5"]

/-
info: []
-/
-- #guard_msgs in
-- #eval duplicates [0, 1, 2, 3, 4, 5]

/-
info: [1, 4]
-/
-- #guard_msgs in
-- #eval duplicates [1, 1, 2, 3, 4, 5, 4]

-- Apps difficulty: introductory
-- Assurance level: unguarded