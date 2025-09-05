Consider the array `[3,6,9,12]`. If we generate all the combinations with repetition that sum to `12`, we get `5` combinations: `[12], [6,6], [3,9], [3,3,6], [3,3,3,3]`. The length of the sub-arrays (such as `[3,3,3,3]` should be less than or equal to the length of the initial array (`[3,6,9,12]`).  

Given an array of positive integers and a number `n`, count all combinations with repetition of integers that sum to `n`. For example: 
```Haskell
find([3,6,9,12],12) = 5.
```

More examples in the test cases. 

Good luck!

If you like this Kata, please try:

[Array combinations](https://www.codewars.com/kata/59e66e48fc3c499ec5000103)

[Sum of prime-indexed elements](https://www.codewars.com/kata/59f38b033640ce9fc700015b)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded