Imagine a triangle of numbers which follows this pattern:

 * Starting with the number "1", "1" is positioned at the top of the triangle. As this is the 1st row, it can only support a single number.
 * The 2nd row can support the next 2 numbers: "2" and "3"
 * Likewise, the 3rd row, can only support the next 3 numbers: "4", "5", "6"
 * And so on; this pattern continues.

```
    1
   2 3
  4 5 6
 7 8 9 10
...
```

Given N, return the sum of all numbers on the Nth Row:

1 <= N <= 10,000

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible