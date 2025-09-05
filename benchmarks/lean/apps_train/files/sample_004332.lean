Given a string (`str`) containing a base-10 integer between `0` and `10000`, convert the integer to its binary representation. At that point, obtain a count of the maximum amount of consecutive 0s. From there, return the count in written form with a capital letter.

In the very first example, we have an argument of `"9"` which is being passed to the method. The binary representation of `9` is `1001` which can be read as: one, zero, zero, one. There are, at most, two consecutive 0s, resulting in the integer `2` as the value of the count. The output in the block of code above reflects the final step of taking `2` from standard form to the written form `"Two"` as prompted.

In the very last example, we have an argument of `"550"` which is being passed to the method. The binary representation of `550` is `1000100110` which can be read as: one, zero, zero, zero, one, zero, zero, one, one, zero. There are, at most, three consecutive 0s, resulting in the integer `3` as the value of the count. The output in the block of code above reflects the final step of taking `3` from standard form to the written form of `"Three"` as prompted.

One way, among many, to visualize the end of each step might look like:
```
max_consec_zeros("777")
1: "777"
2: 777
3: 1100001001
4: 4
5: "Four"
max_consec_zeros("777") => "Four"
```
Happy coding!

def max_consec_zeros (n: String) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
