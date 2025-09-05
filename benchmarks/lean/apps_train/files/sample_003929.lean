In this Kata, you will be given a list of strings and your task will be to find the strings that have the same characters and return the sum of their positions as follows: 

```Haskell
solve(["abc","abbc", "ab", "xyz", "xy", "zzyx"]) = [1,8]
-- we see that the elements at indices 0 and 1 have the same characters, as do those at indices 3 and 5.
-- we therefore return [1,8] because [0+1,3+5] = [1,8]. This result is sorted. 
-- ignore those that don't have at least one matching partner, such as "ab" and "xy".

Another example...
solve(["wkskkkkkk","fokoo","wkskk","uizzzz","fokooff","wkskkkk","uizzzzzzz"]),[5,7,9]);
--The element at index 0 is similar to those at indices 2 and 5; so 0 + 2 + 5 = 7.
--The element at index 1 is similar to that at index 4; so 1 + 4 = 5. 
--The element at index 3 is similar to that at index 6; so 3 + 6 = 9.
--The result must be sorted. We get [5,7,9].
```
More examples in the test cases. 

Good luck!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
