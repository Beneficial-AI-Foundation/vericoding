Write a function that takes a positive integer and returns the next smaller positive integer containing the same digits.

For example:

```python
next_smaller(21) == 12
next_smaller(531) == 513
next_smaller(2071) == 2017
```

Return -1 (for `Haskell`: return `Nothing`, for `Rust`: return `None`), when there is no smaller number that contains the same digits. Also return -1 when the next smaller number with the same digits would require the leading digit to be zero.

```python 
next_smaller(9) == -1
next_smaller(135) == -1
next_smaller(1027) == -1  # 0721 is out since we don't write numbers with leading zeros
```
```ruby 
next_smaller(9) == -1
next_smaller(135) == -1
next_smaller(1027) == -1  # 0721 is out since we don't write numbers with leading zeros
```

 * some tests will include very large numbers.
 * test data only employs positive integers.

*The function you write for this challenge is the inverse of this kata: "[Next bigger number with the same digits](http://www.codewars.com/kata/next-bigger-number-with-the-same-digits)."*

def next_smaller (n : Nat) : Int := sorry

theorem next_smaller_result_positive (n : Nat) (h: n ≥ 10) :
  next_smaller n = -1 ∨ next_smaller n > 0 := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
