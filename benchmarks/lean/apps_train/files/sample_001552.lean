# Task
 You are given integer `n` determining set S = {1, 2, ..., n}. Determine if the number of k-element subsets of S is `ODD` or `EVEN` for given integer k.

# Example

 For `n = 3, k = 2`, the result should be `"ODD"`

 In this case, we have 3 2-element subsets of {1, 2, 3}:

 `{1, 2}, {1, 3}, {2, 3}`

 For `n = 2, k = 1`, the result should be `"EVEN"`.

 In this case, we have 2 1-element subsets of {1, 2}:

 `{1}, {2}`

 `Don't bother with naive solution - numbers here are really big.`

# Input/Output

 - `[input]` integer `n`

    `1 <= n <= 10^9`

 - `[input]` integer `k`

    `1 <= k <= n`

 - `[output]` a string

    `"EVEN"` or `"ODD"` depending if the number of k-element subsets of S = {1, 2, ..., n} is ODD or EVEN.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded