German mathematician Christian Goldbach (1690-1764) [conjectured](https://en.wikipedia.org/wiki/Goldbach%27s_conjecture) that every even number greater than 2 can be represented by the sum of two prime numbers. For example, `10` can be represented as `3+7` or `5+5`.

Your job is to make the function return a list containing all unique possible representations of `n` in an increasing order if `n` is an even integer; if `n` is odd, return an empty list. Hence, the first addend must always be less than or equal to the second to avoid duplicates.

Constraints : `2 < n < 32000` and `n` is even

## Examples
```
26  -->  ['3+23', '7+19', '13+13']

100 -->  ['3+97', '11+89', '17+83', '29+71', '41+59', '47+53']

7   -->  [] 
```

def goldbach_partitions : Nat → List String := sorry

def is_prime : Nat → Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
