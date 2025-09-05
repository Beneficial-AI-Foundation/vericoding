In this Kata, you will be given an array of arrays and your task will be to return the number of unique arrays that can be formed by picking exactly one element from each subarray. 

For example: `solve([[1,2],[4],[5,6]]) = 4`, because it results in only `4` possiblites. They are `[1,4,5],[1,4,6],[2,4,5],[2,4,6]`. 

```if:r
In R, we will use a list data structure.
So the argument for `solve` is a list of numeric vectors.
~~~
solve(list(c(1, 2), 4, c(5, 6)))
[1] 4
~~~
```

Make sure that you don't count duplicates; for example `solve([[1,2],[4,4],[5,6,6]]) = 4`, since the extra outcomes are just duplicates. 

See test cases for more examples.

Good luck!

If you like this Kata, please try:

[Sum of integer combinations](https://www.codewars.com/kata/59f3178e3640cef6d90000d5)

[Sum of array singles](https://www.codewars.com/kata/59f11118a5e129e591000134)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded