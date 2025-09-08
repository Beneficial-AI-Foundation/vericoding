/-
# Background:

You're working in a number zoo, and it seems that one of the numbers has gone missing!

Zoo workers have no idea what number is missing, and are too incompetent to figure it out, so they're hiring you to do it for them.

In case the zoo loses another number, they want your program to work regardless of how many numbers there are in total.

___

## Task:

Write a function that takes a shuffled list of unique numbers from `1` to `n` with one element missing (which can be any number including `n`). Return this missing number.

**Note**: huge lists will be tested.

## Examples:

```
[1, 3, 4]  =>  2
[1, 2, 3]  =>  4
[4, 2, 3]  =>  1
```
-/

-- <vc-helpers>
-- </vc-helpers>

def find_missing_number (nums : List Nat) : Nat := sorry

theorem find_missing_number_sequence (n : Nat) (h : 0 < n) (h2 : n ≤ 1000) : 
  let nums := (List.range n).map (· + 1)
  let nums_without_last := nums.dropLast
  find_missing_number nums_without_last = n := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_missing_number [1, 3, 4]

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_missing_number [1, 2, 3]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_missing_number [2, 3, 4]

-- Apps difficulty: introductory
-- Assurance level: guarded