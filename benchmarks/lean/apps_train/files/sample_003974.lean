# Task
 Given an array `arr` and a number `n`. Call a pair of numbers from the array a `Perfect Pair` if their sum is equal to `n`.

 Find all of the perfect pairs and return the sum of their **indices**. 

 Note that any element of the array can only be counted in one Perfect Pair. Also if there are multiple correct answers, return the smallest one.

# Example

 For `arr = [1, 4, 2, 3, 0, 5] and n = 7`, the result should be `11`.

 Since the Perfect Pairs are `(4, 3)` and `(2, 5)` with indices `1 + 3 + 2 + 5 = 11`.

 For `arr = [1, 3, 2, 4] and n = 4`, the result should be `1`.

 Since the element at `index 0` (i.e. 1) and the element at `index 1` (i.e. 3) form the only Perfect Pair.

# Input/Output

 - `[input]` integer array `arr`

  array of non-negative integers.

 - `[input]` integer `n`

  positive integer

 - `[output]` integer

  sum of indices and 0 if no Perfect Pair exists.

def pairwise_pairs : List Int → Int → List (Int × Int)
| xs, n => sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
