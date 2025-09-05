# Task

Given a square `matrix`, your task is to reverse the order of elements on both of its longest diagonals.

The longest diagonals of a square matrix are defined as follows:
* the first longest diagonal goes from the top left corner to the bottom right one;
* the second longest diagonal goes from the top right corner to the bottom left one.

# Example

For the matrix
```
1, 2, 3
4, 5, 6
7, 8, 9
```
the output should be:
```
9, 2, 7
4, 5, 6
3, 8, 1
```

# Input/Output

- `[input]` 2D integer array `matrix`

   Constraints: `1 ≤ matrix.length ≤ 10, matrix.length = matrix[i].length, 1 ≤ matrix[i][j] ≤ 1000`

- `[output]` 2D integer array

   Matrix with the order of elements on its longest diagonals reversed.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded