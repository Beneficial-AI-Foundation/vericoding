# Task
 Given a rectangular matrix containing only digits, calculate the number of different `2 × 2` squares in it.

# Example

 For
```
matrix = [[1, 2, 1],
          [2, 2, 2],
          [2, 2, 2],
          [1, 2, 3],
          [2, 2, 1]]
```
the output should be `6`.

 Here are all 6 different 2 × 2 squares:

 ```
 1 2
 2 2

 2 1
 2 2

 2 2
 2 2

 2 2
 1 2

 2 2
 2 3

 2 3
 2 1
 ```

# Input/Output

 - `[input]` 2D integer array `matrix`

    Constraints: 

    `1 ≤ matrix.length ≤ 100,`

    `1 ≤ matrix[i].length ≤ 100,`

    `0 ≤ matrix[i][j] ≤ 9.`

 - `[output]` an integer

    The number of different `2 × 2` squares in matrix.

def Matrix := List (List Nat)

def different_squares : Matrix → Nat := sorry

def rotateMatrix (m : Matrix) : Matrix := sorry

def isValidMatrix (m : Matrix) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
