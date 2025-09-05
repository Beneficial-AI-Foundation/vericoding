# Task
 Consider the following operation:

 We take a positive integer `n` and replace it with the sum of its `prime factors` (if a prime number is presented multiple times in the factorization of `n`, then it's counted the same number of times in the sum). 

 This operation is applied sequentially first to the given number, then to the first result, then to the second result and so on.., until the result remains the same.

  Given number `n`, find the final result of the operation.

# Example

  For `n = 24`, the output should be `5`.
```
24 -> (2 + 2 + 2 + 3) = 9 -> (3 + 3) = 6 -> (2 + 3) = 5 -> 5.
So the answer for n = 24 is 5.```

# Input/Output

 - `[input]` integer `n`

  Constraints: `2 ≤ n ≤ 10000.`

 - `[output]` an integer

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
