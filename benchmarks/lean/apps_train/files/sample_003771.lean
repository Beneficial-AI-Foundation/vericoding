Write a function that returns the number of '2's in the factorization of a number.  
For example,
```python
two_count(24)
```
should return 3, since the factorization of 24 is 2^3 x 3
```python
two_count(17280)
```
should return 7, since the factorization of 17280 is 2^7 x 5 x 3^3  
The number passed to two_count (twoCount)  will always be a positive integer greater than or equal to 1.

def two_count (n : Nat) : Nat := sorry 

theorem two_count_non_negative (n : Nat) (h : n > 0) : 
  two_count n ≥ 0 := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded