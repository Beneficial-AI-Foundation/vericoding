We are interested in collecting the sets of six prime numbers, that having a starting prime p, the following values are also primes forming the sextuplet ```[p, p + 4, p + 6, p + 10, p + 12, p + 16]```

The first sextuplet that we find is ```[7, 11, 13, 17, 19, 23]```

The second one is ```[97, 101, 103, 107, 109, 113]```

Given a number ```sum_limit```, you should give the first sextuplet which sum (of its six primes) surpasses the sum_limit value.

```python
find_primes_sextuplet(70) == [7, 11, 13, 17, 19, 23]

find_primes_sextuplet(600) == [97, 101, 103, 107, 109, 113]
```
Features of the tests:
```
Number Of Tests = 18
10000 < sum_limit < 29700000
```
If you have solved this kata perhaps you will find easy to solve this one:
https://www.codewars.com/kata/primes-with-two-even-and-double-even-jumps/
Enjoy it!!

def findPrimesSextuplet (limit : Nat) : List Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
