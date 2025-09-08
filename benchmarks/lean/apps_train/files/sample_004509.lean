/-
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
-/

def rotate_clockwise (m : Matrix) : Matrix :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def manual_rotate (m : Matrix) : Matrix :=
  sorry

theorem empty_matrix_rotation :
  ∀ (m : Matrix), m.content = [] → (rotate_clockwise m).content = [] :=
  sorry

theorem rotation_dimensions {m : Matrix} (h1 : m.content ≠ []) 
    (h2 : ∃ s, m.content.head? = some s) (h3 : ∀ s, m.content.head? = some s → s ≠ "") :
    let rotated := rotate_clockwise m
    let first := Classical.choose h2
    (rotated.content.length = first.length) ∧
    (∀ (row : String), row ∈ rotated.content → row.length = m.content.length) :=
  sorry

theorem four_rotations_identity {m : Matrix} (h1 : m.content ≠ [])
    (h2 : ∃ s, m.content.head? = some s) (h3 : ∀ s, m.content.head? = some s → s ≠ "") :
    rotate_clockwise (rotate_clockwise (rotate_clockwise (rotate_clockwise m))) = m :=
  sorry

theorem rotation_equals_manual :
  ∀ (m : Matrix), rotate_clockwise m = manual_rotate m :=
  sorry

-- Apps difficulty: introductory
-- Assurance level: guarded