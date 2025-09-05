Given a certain square matrix ```A```, of dimension ```n x n```, that has negative and positive values (many of them may be 0).

We need the following values rounded to the closest integer:

- the average of all the positive numbers (more or equal to 0) that are in the principal diagonal and in the columns with odd index, **avg1**

- the absolute value of the average of all the negative numbers in the secondary diagonal and in the columns with even index, **avg2**

Let's see the requirements in an example:
```
A = [[ 1,   3, -4,   5, -2,  5,  1], 
    [  2,   0, -7,   6,  8,  8, 15],
    [  4,   4, -2, -10,  7, -1,  7],
    [ -1,   3,  1,   0, 11,  4, 21],
    [ -7,   6, -4,  10,  5,  7,  6],
    [ -5,   4,  3,  -5,  7,  8, 17],
    [-11,   3,  4,  -8,  6, 16,  4]]
```    
The elements of the principal diagonal are: 
```
[1, 0, -2, 0, 5, 8, 4]
```
The ones that are also in the "odd columns" (we consider the index starting with 0) are: 
```
[0, 0, 8] all positives
```
So,
```
avg1 =  [8 / 3] = 3
```
The elements of the secondary diagonal are:
```
[-11, 4, -4, 0, 7, 8, 1]
```
The ones that are in the even columns are:
```
[-11, -4, 7, 1]
```
The negative ones are:
```
[-11, 4]
```
So,
```
avg2 = [|-15 / 2|] = 8
```
Create a function ```avg_diags()```that may receive a square matrix of uncertain dimensions and may output both averages in an array in the following order: ```[avg1, avg2]```

If one of the diagonals have no elements fulfilling the requirements described above the function should return ```-1```
So, if the function processes the matrix given above, it should output:
```
[3, 8]
```
Features of the random tests:
```
number of tests = 110
5 ≤ matrix_length ≤ 1000
-1000000 ≤ matrix[i, j] ≤ 1000000
```
Enjoy it!
Translations into another languages will be released soon.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
