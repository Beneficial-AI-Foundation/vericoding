##Background - the Collatz Conjecture:

Imagine you are given a positive integer, `n`, then:

* if `n` is even, calculate: `n / 2`
* if `n` is odd, calculate: `3 * n + 1`

Repeat until your answer is `1`. The Collatz conjecture states that performing this operation repeatedly, you will always eventually reach `1`.

You can try creating Collatz sequences with [this](http://www.codewars.com/kata/5286b2e162056fd0cb000c20) kata. For further information, see the [wiki page](https://en.wikipedia.org/wiki/Collatz_conjecture).

##Now! Your task:

**Given an array of positive integers, return the integer whose Collatz sequence is the longest.**

Example:

```python
longest_collatz([2, 4, 3])==3
```

Explanation: The Collatz sequence for `2` has a length of `1`, the sequence for `4` has a length of `2`, and the sequence for `3` has a length of `7`. So from our array, the integer `3` is the one with the longest Collatz sequence.

Hence, your function should return `3`.

##Note:

There may be more than one answer, i.e. two or more integers produce the longest Collatz sequence, because they happen to have sequences of the same length. **In this case, your function should return the integer that appears first in the array.**

Example:
Given an array: `[2, 5, 32]`, both `5` and `32` have Collatz sequences of length 5. These are also the longest sequences from our array.

In this case, our function returns `5`, because `5` comes before `32` in our array.

def collatzLength (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded