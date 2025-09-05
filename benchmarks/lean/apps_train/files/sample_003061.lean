The sum of divisors of `6` is `12` and the sum of divisors of `28` is `56`. You will notice that `12/6 = 2` and `56/28 = 2`. We shall say that `(6,28)` is a pair with a ratio of `2`.  Similarly, `(30,140)` is also a pair but with a ratio of `2.4`. These ratios are simply decimal representations of fractions.

`(6,28)` and `(30,140)` are the only pairs in which `every member of a pair is 0 <= n < 200`. The sum of the lowest members of each pair is `6 + 30 = 36`. 

You will be given a `range(a,b)`, and your task is to group the numbers into pairs with the same ratios. You will return the sum of the lowest member of each pair in the range. If there are no pairs. return `nil` in Ruby, `0` in python. Upper limit is `2000`.

```Haskell
solve(0,200) = 36
```

Good luck!

if you like this Kata, please try:

[Simple division](https://www.codewars.com/kata/59ec2d112332430ce9000005)

[Sub-array division](https://www.codewars.com/kata/59eb64cba954273cd4000099)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded