We have a matrix of integers with m rows and n columns.

We want to calculate the total sum for the matrix:

As you can see, the name "alternating sum" of the title is due to the sign of the terms that changes from one term to its contiguous one and so on.

Let's see an example:
```
matrix = [[1, 2, 3], [-3, -2, 1], [3, - 1, 2]]

total_sum = (1 - 2 + 3) + [-(-3) + (-2) - 1] + [3 - (-1) + 2] = 2 + 0 + 6 = 8
```
You may be given matrixes with their dimensions between these values:```10 < m < 300``` and ```10 < n < 300```.

More example cases in the Example Test Cases.
Enjoy it!!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
