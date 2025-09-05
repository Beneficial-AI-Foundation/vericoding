## Problem

Determine whether a positive integer number is **colorful** or not.

`263` is a colorful number because `[2, 6, 3, 2*6, 6*3, 2*6*3]` are all different; whereas `236` is not colorful, because `[2, 3, 6, 2*3, 3*6, 2*3*6]` have `6` twice.

So take all consecutive subsets of digits, take their product and ensure all the products are different.

## Examples
```pyhton
263  -->  true
236  -->  false
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
