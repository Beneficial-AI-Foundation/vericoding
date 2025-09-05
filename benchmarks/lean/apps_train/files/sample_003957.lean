[Langton's ant](https://en.wikipedia.org/wiki/Langton%27s_ant) is a two-dimensional Turing machine invented in the late 1980s. The ant starts out on a grid of black and white cells and follows a simple set of rules that has complex emergent behavior.

## Task

Complete the function and return the `n`th iteration of Langton's ant with the given input.

### Parameters:

* `grid` - a two dimensional array of `1`s and `0`s (representing white and black cells respectively)
* `column` - horizontal position of ant
* `row` - ant's vertical position
* `n` - number of iterations
* `dir` - ant's current direction (0 - north, 1 - east, 2 - south, 3 - west), **should default to 0**

**Note:** parameters `column` and `row` will always be inside the `grid`, and number of generations `n` will never be negative.

## Output

The state of the `grid` after `n` iterations.

## Rules

The ant can travel in any of the four cardinal directions at each step it takes. The ant moves according to the rules below:

* At a white square (represented with `1`), turn 90° right, flip the color of the square, and move forward one unit.
* At a black square (`0`), turn 90° left, flip the color of the square, and move forward one unit.

The grid has no limits and therefore if the ant moves outside the borders, the grid should be expanded with `0`s, respectively maintaining the rectangle shape.

## Example

```python
ant([[1]], 0, 0, 1, 0)   # should return: [[0, 0]]
```

Initially facing north (`0`), at the first iteration the ant turns right (because it stands on a white square, `1`), flips the square and moves forward.

def ant (grid : List (List Int)) (col : Int) (row : Int) (steps : Int)
  (direction : Int := 0) : List (List Int) := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
