/-
# Task
For the given set `S` its powerset is the set of all possible subsets of `S`.

Given an array of integers nums, your task is to return the powerset of its elements.

Implement an algorithm that does it in a depth-first search fashion. That is, for every integer in the set, we can either choose to take or not take it. At first, we choose `NOT` to take it, then we choose to take it(see more details in exampele).

# Example

For `nums = [1, 2]`, the output should be `[[], [2], [1], [1, 2]].`

Here's how the answer is obtained:
```
don't take element 1
----don't take element 2
--------add []
----take element 2
--------add [2]
take element 1
----don't take element 2
--------add [1]
----take element 2
--------add [1, 2]```

For `nums = [1, 2, 3]`, the output should be 

`[[], [3], [2], [2, 3], [1], [1, 3], [1, 2], [1, 2, 3]]`.

# Input/Output

`[input]` integer array `nums`

Array of positive integers, `1 ≤ nums.length ≤ 10`.

[output] 2D integer array

The powerset of nums.
-/

-- <vc-helpers>
-- </vc-helpers>

def powerset {α : Type} (l : List α) : List (List α) :=
  sorry

theorem powerset_length {α : Type} (l : List α) : 
  (powerset l).length = 2 ^ l.length := by
  sorry

theorem powerset_contains_empty {α : Type} (l : List α) :
  [] ∈ powerset l := by
  sorry

theorem powerset_contains_full {α : Type} (l : List α) (h : l ≠ []) :
  l ∈ powerset l := by
  sorry

theorem powerset_elements_are_lists {α : Type} (l : List α) :
  ∀ x ∈ powerset l, x matches List.cons _ _ ∨ x = [] := by
  sorry

theorem powerset_subsets {α : Type} [BEq α] (l : List α) :
  ∀ subset ∈ powerset l, ∀ x ∈ subset, x ∈ l := by
  sorry

/-
info: [[], [2], [1], [1, 2]]
-/
-- #guard_msgs in
-- #eval powerset [1, 2]

/-
info: [[], [3], [2], [2, 3], [1], [1, 3], [1, 2], [1, 2, 3]]
-/
-- #guard_msgs in
-- #eval powerset [1, 2, 3]

/-
info: [[], [1]]
-/
-- #guard_msgs in
-- #eval powerset [1]

-- Apps difficulty: introductory
-- Assurance level: guarded