/-
If this challenge is too easy for you, check out: 
https://www.codewars.com/kata/5cc89c182777b00001b3e6a2

___

Upside-Down Pyramid Addition is the process of taking a list of numbers and consecutively adding them together until you reach one number.

When given the numbers `2, 1, 1` the following process occurs:
```
 2   1   1
   3   2 
     5
```

This ends in the number `5`.

___

### YOUR TASK

Given the right side of an Upside-Down Pyramid (Ascending), write a function that will return the original list.

### EXAMPLE

```python
reverse([5, 2, 1]) == [2, 1, 1]
```

NOTE: The Upside-Down Pyramid will never be empty and will always consist of positive integers ONLY.
-/

-- <vc-helpers>
-- </vc-helpers>

def reverse (nums : List Int) : List Int := sorry

theorem reverse_length_preservation {nums : List Int} :
  (List.length (reverse nums)) = (List.length nums) := sorry

theorem reverse_nonempty_preservation {nums : List Int} :
  nums ≠ [] → reverse nums ≠ [] := sorry

theorem reverse_last_element_preservation {nums : List Int} (h : nums ≠ []) :
  List.getLast nums h = List.getLast (reverse nums) (reverse_nonempty_preservation h) := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval reverse [5, 2, 1]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval reverse [84, 42, 21, 10, 2]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval reverse [83, 47, 28, 16, 7]

-- Apps difficulty: introductory
-- Assurance level: unguarded