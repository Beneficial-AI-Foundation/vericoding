# Task
Two arrays are called similar if one can be obtained from another by swapping at most one pair of elements.

Given two arrays, check whether they are similar.

# Example

For `A = [1, 2, 3]` and `B = [1, 2, 3]`, the output should be `true;`

For `A = [1, 2, 3]` and `B = [2, 1, 3]`, the output should be `true;`

For `A = [1, 2, 2]` and `B = [2, 1, 1]`, the output should be `false.`

# Input/Output

- `[input]` integer array `A`

Array of integers.

Constraints: `3 ≤ A.length ≤ 10000, 1 ≤ A[i] ≤ 1000.`

- `[input]` integer array `B`

Array of integers of the same length as `A`.

Constraints: `B.length = A.length, 1 ≤ B[i] ≤ 1000.`

- `[output]` a boolean value

`true` if `A` and `B` are similar, `false` otherwise.

def are_similar (xs ys : List Int) : Bool := sorry

theorem identical_lists_are_similar {xs : List Int} (h : xs ≠ []) : 
  are_similar xs xs := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
