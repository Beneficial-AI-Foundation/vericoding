Given a triangle of consecutive odd numbers:

```
             1
          3     5
       7     9    11
   13    15    17    19
21    23    25    27    29
...
```

find the triangle's row knowing its index (the rows are 1-indexed), e.g.:

```
odd_row(1)  ==  [1]
odd_row(2)  ==  [3, 5]
odd_row(3)  ==  [7, 9, 11]
```

**Note**: your code should be optimized to handle big inputs.

___

The idea for this kata was taken from this kata: [Sum of odd numbers](https://www.codewars.com/kata/sum-of-odd-numbers)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible