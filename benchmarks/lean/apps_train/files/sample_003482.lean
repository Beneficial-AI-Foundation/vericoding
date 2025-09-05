We define the score of permutations of combinations, of an integer number (the function to obtain this value:```sc_perm_comb```) as the total sum of all the numbers obtained from the permutations of all the possible combinations of its digits.
For example we have the number 348.
```python
sc_perm_comb(348) = 3 + 4 + 8 + 34 + 38 + 48 + 43 + 83 + 84 + 348 + 384 + 834 + 843 + 438 + 483  = 3675
```
If the number has a digit 0, the numbers formed by a leading 0 should be discarded:
```python
sc_perm_comb(340) = 3 + 4 + 34 + 30 + 40 + 43 + 340 + 304 + 430 + 403 = 1631
```
If the number has digits that occur more than once, the score the adden will not be taken than twice or more:
```python
sc_perm_comb(333) = 3 + 33 + 333 = 369
```
If the number has only one digit its score is the same number:
```python
sc_perm_comb(6) = 6
sc_perm_comb(0) = 0
```

Enjoy it!!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded