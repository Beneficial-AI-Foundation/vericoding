# Task

Given an array of integers, sum consecutive even numbers and consecutive odd numbers. Repeat the process while it can be done and return the length of the final array.

# Example

For `arr = [2, 1, 2, 2, 6, 5, 0, 2, 0, 5, 5, 7, 7, 4, 3, 3, 9]`

The result should be `6`.

```
[2, 1, 2, 2, 6, 5, 0, 2, 0, 5, 5, 7, 7, 4, 3, 3, 9]  -->
         2+2+6       0+2+0     5+5+7+7       3+3+9
[2, 1,   10,    5,    2,        24,     4,   15   ] -->
                               2+24+4
[2, 1,   10,    5,             30,           15   ]
The length of final array is 6
```

# Input/Output

- `[input]` integer array `arr`

  A non-empty array, 

  `1 ≤ arr.length ≤ 1000`

  `0 ≤ arr[i] ≤ 1000`

- `[output]` an integer

  The length of the final array

def sumGroups (arr : List Int) : Int := sorry

def getNextArr (arr : List Int) : List Int := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded