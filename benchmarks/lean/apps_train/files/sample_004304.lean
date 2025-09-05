# Task
 You are given an array of integers `a` and a non-negative number of operations `k`, applied to the array. Each operation consists of two parts:
```
find the maximum element value of the array;
replace each element a[i] with (maximum element value - a[i]).```
How will the array look like after `k` such operations?

# Example

 For `a = [-4, 0, -1, 0]` and `k = 2`, the output should be `[0, 4, 3, 4]`.
 ```
 initial array: [-4, 0, -1, 0]
 1st operation: 
 find the maximum value --> 0
 replace each element:  --> [(0 - -4), (0 - 0), (0 - -1), (0 - 0)]
                        --> [4, 0, 1, 0]
 2nd operation: 
 find the maximum value --> 4
 replace each element:  --> [(4 - 4), (4 - 0), (4 - 1), (4 - 0)]
                        --> [0, 4, 3, 4]

 ```
 For `a = [0, -1, 0, 0, -1, -1, -1, -1, 1, -1]` and `k = 1`, 

 the output should be `[1, 2, 1, 1, 2, 2, 2, 2, 0, 2]`.
 ```
 initial array: [0, -1, 0, 0, -1, -1, -1, -1, 1, -1]
 1st operation: 
 find the maximum value --> 1
 replace each element:  -->
 [(1-0),(1- -1),(1-0),(1-0),(1- -1),(1- -1),(1- -1),(1- -1),(1-1),(1- -1)]
--> [1, 2, 1, 1, 2, 2, 2, 2, 0, 2]
 ```

# Input/Output

 - `[input]` integer array a

    The initial array.

    Constraints: 

    `1 <= a.length <= 100`

    `-100 <= a[i] <= 100`

 - `[input]` integer `k`

    non-negative number of operations.

    Constraints: `0 <= k <= 100000`

 - [output] an integer array

    The array after `k` operations.

def List.maximum' (l : List Int) (h : l ≠ []) : Int :=
  match l with
  | [] => by contradiction
  | x :: xs => xs.foldl max x

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible