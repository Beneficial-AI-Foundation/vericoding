Related to MrZizoScream's Product Array kata. You might want to solve that one first :)

```if:javascript
**Note:** Node 10 has now been enabled, and you can now use its BigInt capabilities if you wish, though your resulting array must still contain strings (e.g. "99999999999", not 9999999999n)

Pre-node 10: You will need to use the BigNumber.js library! Please use `.toFixed(0)` or `.toPrecision()` to round instead of `.toString(10)`, as the latter is _very_ slow
```

This is an adaptation of a problem I came across on LeetCode. 

Given an array of numbers, your task is to return a new array where each index (`new_array[i]`) is equal to the product of the original array, except for the number at that index (`array[i]`).

**Two things to keep in mind:**

* Zeroes will be making their way into some of the arrays you are given
* O(n^2) solutions will not pass.

Examples:

**Note**: All inputs will be valid arrays of nonzero length.

Have fun! Please upvote if you enjoyed :)

def List.product (l : List Int) : Int := sorry 

def product_sans_n (nums : List Int) : List Int := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
