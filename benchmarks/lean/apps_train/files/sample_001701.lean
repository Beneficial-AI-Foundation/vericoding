Given a set of integers _S_, the _closure of S under multiplication_ is the smallest set that contains _S_ and such that for any _x, y_ in the closure of _S_, the product _x * y_ is also in the closure of _S_. 

Example 1: Given `S = {2}`, the closure of `S` is the set `{2, 4, 8, 16, 32, 64, ... }`.

Example 2: Given `S = {1, 2, 3}`, the closure of `S` is the set `{1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27, 32, 36, ...}`. This set contains, e.g, `6` because `6 = 2 * 3`. It further contains `12` and `18` because `12 = 2 * 6` and `18 = 3 * 6`. Etc. 

Example 3: Given `S` the set of prime numbers, the closure of `S` is the set of all positive integers greater than or equal to `2`. 

Your task is two write a generator function that generates the members of the closure of any given _finite_ set of positive numbers `S` in _ascending order_.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded