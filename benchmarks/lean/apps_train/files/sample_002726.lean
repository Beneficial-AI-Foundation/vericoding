# Task
 You have two sorted arrays `a` and `b`, merge them to form new array of unique items.

 If an item is present in both arrays, it should be part of the resulting array if and only if it appears in both arrays the same number of times.

# Example

  For `a = [1, 3, 40, 40, 50, 60, 60, 60]` and `b = [2, 40, 40, 50, 50, 65]`, the result should be `[1, 2, 3, 40, 60, 65]`.
```
Number 40 appears 2 times in both arrays, 
thus it is in the resulting array.
Number 50 appears once in array a and twice in array b, 
therefore it is not part of the resulting array.```

# Input/Output

 - `[input]` integer array `a`

 A sorted array.

 1 ≤ a.length ≤ 500000

 - `[input]` integer array `b`

 A sorted array.

 `1 ≤ b.length ≤ 500000`

- `[output]` an integer array

  The resulting sorted array.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
