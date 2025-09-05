# Problem Description

Let's imagine a function `F(n)`, which is defined over the integers
in the range of `1 <= n <= max_n`, and `0 <= F(n) <= max_fn` for every `n`.

There are `(1 + max_fn) ** max_n` possible definitions of `F` in total.

Out of those definitions, how many `F`s satisfy the following equations?
Since your answer will be very large, please give your answer **modulo 12345787**.

* `F(n) + F(n + 1) <= max_fn` for `1 <= n < max_n`
* `F(max_n) + F(1) <= max_fn`

# Constraints

`1 <= max_n <= 100`

`1 <= max_fn <= 5`

The inputs will be always valid integers.

# Examples

```python
# F(1) + F(1) <= 1, F(1) = 0
circular_limited_sums(1, 1) == 1

# F = (0, 0), (0, 1), (1, 0)
circular_limited_sums(2, 1) == 3

# F = (0, 0, 0), (0, 0, 1), (0, 1, 0), (1, 0, 0)
circular_limited_sums(3, 1) == 4

# F = (0, 0, 0, 0), (0, 0, 0, 1), (0, 0, 1, 0), (0, 1, 0, 0),
# (0, 1, 0, 1), (1, 0, 0, 0), (1, 0, 1, 0)
circular_limited_sums(4, 1) == 7

# F = (0), (1)
circular_limited_sums(1, 2) == 2
# F = (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0)
circular_limited_sums(2, 2) == 6
# F = (0, 0, 0), (0, 0, 1), (0, 0, 2), (0, 1, 0), (0, 1, 1),
# (0, 2, 0), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1), (2, 0, 0)
circular_limited_sums(3, 2) == 11
circular_limited_sums(4, 2) == 26
```

# Acknowledgement

This problem was designed as a hybrid of [Project Euler #209: Circular Logic](https://projecteuler.net/problem=209) and [Project Euler #164: Numbers for which no three consecutive digits have a sum greater than a given value](https://projecteuler.net/problem=164).

If you enjoyed this Kata, please also have a look at [my other Katas](https://www.codewars.com/users/Bubbler/authored)!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
