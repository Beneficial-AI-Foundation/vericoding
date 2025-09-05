We need a function that may receive a list  of an unknown amount of points in the same plane, having each of them, cartesian coordinates of the form (x, y) and may find the biggest triangle (the one with the largest area) formed by all of the possible combinations of groups of three points of that given list.
Of course, we will have some combinations of three points that does not form a triangle, because the three points are aligned.
The function find_biggTriang(listOfPoints), will output a list with the following data in the order presented bellow:
```python
[(1), (2), (3), (4), 5]

(1) - Number of points received (You may assume that you will not receive duplicates)

(2) - Maximum possible amount of triangles that can be formed with the amount of received 
      points (number in data (1) above). It should be expressed as an integer, (no L for long type 
      variables)

(3) - Real Number of triangles that can be formed with the given points. (The function should have a 
      counter for all the cases of three points aligned). It should be expressedas as an integer.

(4) - The triangles that have maximum area in a sorted list. 
      If there are two triangles with the biggest area, the result will be presented in this way:
      [[[xA1, yA1], [xB1, yB1], [xC1, yC1]], [[xA2, yA2], [xB2, yB2], [xC2, yC2]]]
      But if we have only one triangle with max. area, there is no need of a spare level of braces, 
      so it will be as follows: [[xA1, yA1], [xB1, yB1], [xC1, yC1]]

(5) - The value of max. area (absolute value) that was found as a float. As we did not define the 
      units of length for the coordinates, the units for the area will be ignored.

```

It would be useful to apply the expression for the area of a triangle with vertices A, B, and C, is equal to the half of the determinant of the matrix, using the respective coordinates as follows:

```python

                               | xA    yA    1|
Area Triangle(A, B, C) = 1/2 . | xB    yB    1|
                               | xC    yC    1|

```
The negative sign for the area should be ignored for the purpose of the exercise, and we will consider the absolute value for all cases.

See how to calculate the determinant of a matrix 3 x 3, rule of Sarrus.
https://en.wikipedia.org/wiki/Rule_of_Sarrus

Using this expression, it would be easy to detect the cases when three points are aligned.

Let's see some simple cases.
```python
listOfPoints1 = [(0, 1), (7, 3), (9, 0), (7, 10), (2, 9), (10, 7), (2, 8), (9, 8), (4, 4), (2, 10), (10, 1), (0, 4), (4, 3), (10, 0), (0, 3), (3, 4), (1, 1), (7, 2), (4, 0)] (19 points received)

find_biggTriang(listOfPoints1) --------> [19, 969, 953, [[0, 1], [7, 10], [10, 0]], 48.5]

/// Combinations (19, 3) = 969 (We do not have repeated points)
   953 real cases for triangles because the function detected 16 cases when three points are       
   aligned.
   The function found one triangle [[0, 1], [7, 10], [10, 0]] with its area equals to 49.5///

listOfPoints2 = [(7, 4), (0, 0), (9, 10), (5, 0), (8, 1), (7, 6), (9, 3), (2, 4), (6, 3), (5, 6), (3, 6), (10, 0), (9, 7), (3, 10), (10, 2)] (15 points received)

find_biggTriang(listOfPoints2) --------> [15, 455, 446, [[[0, 0], [9, 10], [10, 0]], [[0, 0], [10, 0], [3, 10]]], 50.0]

/// Combinations(15, 3) = 455 but there were only 446 real triangles
   We found two triangles: [[0, 0], [9, 10], [10, 0]] and [[0, 0], [10, 0], [3, 10]] (both in a 
   sorted list. Both triangles have an area of 50.0///
```
Your code will be tested with lists created randomly up to 70 points.

Have a nice moment and enjoy it!!

def Point := (Int × Int)
def Triangle := (Point × Point × Point)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded