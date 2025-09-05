## Number pyramid

Number pyramid is a recursive structure where each next row is constructed by adding adjacent values of the current row. For example:

```
Row 1     [1     2     3     4]
Row 2        [3     5     7]
Row 3           [8    12]
Row 4             [20]
```

___

## Task

Given the first row of the number pyramid, find the value stored in its last row.

___

## Examples

```python
reduce_pyramid([1])        ==  1
reduce_pyramid([3, 5])     ==  8
reduce_pyramid([3, 9, 4])  ==  25
```

___

## Performance tests

```python
Number of tests: 10
List size: 10,000
```

def reducePyramid (base : List Int) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded