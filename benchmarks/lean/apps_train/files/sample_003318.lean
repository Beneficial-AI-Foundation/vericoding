A [perfect power](https://en.wikipedia.org/wiki/Perfect_power) is a classification of positive integers:

> In mathematics, a **perfect power** is a positive integer that can be expressed as an integer power of another positive integer. More formally, n is a perfect power if there exist natural numbers m > 1, and k > 1 such that m^(k) = n.

Your task is to check wheter a given integer is a perfect power. If it is a perfect power, return a pair `m` and `k` with m^(k) = n as a proof. Otherwise return `Nothing`, `Nil`, `null`, `NULL`, `None` or your language's equivalent.

**Note:** For a perfect power, there might be several pairs. For example `81 = 3^4 = 9^2`, so `(3,4)` and `(9,2)` are valid solutions. However, the tests take care of this, so if a number is a perfect power, return any pair that proves it.

### Examples
```python
isPP(4) => [2,2]
isPP(9) => [3,2]
isPP(5) => None
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded