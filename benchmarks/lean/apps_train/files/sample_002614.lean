We are given a sequence of coplanar points and see all the possible triangles that may be generated which all combinations of three points.

We have the following list of points with the cartesian coordinates of each one:
```
Points [x, y]
   A   [1, 2]
   B   [3, 3]
   C   [4, 1]
   D   [1, 1]
   E   [4, -1]
```
With these points we may have the following triangles: ```ABC, ABD, ABE, ACD, ACE, ADE, BCD, BCE, BDE, CDE.``` There are three special ones: ```ABC, ACD and CDE```, that have an angle of 90°. All is shown in the picture below:

We need to count all the rectangle triangles that may be formed by a given list of points.

The case decribed above will be:
```python
count_rect_triang([[1, 2],[3, 3],[4, 1],[1, 1],[4, -1]]) == 3
```

Observe this case:
```python
count_rect_triang([[1, 2],[4, -1],[3, 3],[4, -1],[4, 1],[1, 1],[4, -1], [4, -1], [3, 3], [1, 2]]) == 3
```
If no rectangle triangles may be generated the function will output ```0```.

Enjoy it!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded