# Task
 Imagine a white rectangular grid of `n` rows and `m` columns divided into two parts by a diagonal line running from the upper left to the lower right corner. Now let's paint the grid in two colors according to the following rules:
```
 A cell is painted black if it has at least one point in common with the diagonal;
Otherwise, a cell is painted white.
```
 Count the number of cells painted black.

# Example

 For n = 3 and m = 4, the output should be `6`

 There are 6 cells that have at least one common point with the diagonal and therefore are painted black.

 For n = 3 and m = 3, the output should be `7`

 7 cells have at least one common point with the diagonal and are painted black.

# Input/Output

 - `[input]` integer `n`

   The number of rows.

   Constraints: 1 ≤ n ≤ 10000.

 - `[input]` integer `m`

   The number of columns.

   Constraints: 1 ≤ m ≤ 10000.

 - `[output]` an integer

   The number of black cells.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
