Given a matrix represented as a list of string, such as
```
###.....
..###...
....###.
.....###
.....###
....###.
..###...
###.....
```
write a function
```if:javascript
`rotateClockwise(matrix)`
```
```if:ruby,python
`rotate_clockwise(matrix)`
```
that return its 90° clockwise rotation, for our example:

```
#......#
#......#
##....##
.#....#.
.##..##.
..####..
..####..
...##...
```
>  /!\  You must return a **rotated copy** of `matrix`! (`matrix` must be the same before and after calling your function)  
> Note that the matrix isn't necessarily a square, though it's always a rectangle!  
> Please also note that the equality `m == rotateClockwise(rotateClockwise(rotateClockwise(rotateClockwise(m))));` (360° clockwise rotation), is not always true because `rotateClockwise([''])` => `[]` and `rotateClockwise(['','',''])` => `[]` (empty lines information is lost)

def rotate_clockwise (m : Matrix) : Matrix :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded