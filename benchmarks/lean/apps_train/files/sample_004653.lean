# Toggling Grid
You are given a grid (2d array) of 0/1's. All 1's represents a solved puzzle. Your job is to come up with a sequence of toggle moves that will solve a scrambled grid.

Solved:

```
[ [1, 1, 1],
  [1, 1, 1],
  [1, 1, 1] ]
``` 

"0" (first row) toggle:
```
[ [0, 0, 0],
  [1, 1, 1],
  [1, 1, 1] ]
```

then "3" (first column) toggle:
```
[ [1, 0, 0],
  [0, 1, 1],
  [0, 1, 1] ]
```

The numbers in quotes are codes for the row/column, and will be explained.

## Your task: findSolution()
Your task is to write a function, `findSolution()` (or `find_solution()`), which takes as input a 2d array, and returns an array of "steps" that represent a sequence of toggles to solve the puzzle.

For example:

```python
solution = find_solution(puzzle)
print(solution);
> [0, 3]
```
Note that, in the above example, `[1, 2, 4, 5]` is also a valid solution! Any solution will pass the tests.

The solution is tested like this, for each number in the solution:

```python
if n < puzzle.size:
  toggleRow(n)
else:
  toggleCol(n - puzzle.size)
```
To elaborate, possible n's for a 3x3 puzzle:

- Row numbers = (0    --> size - 1)
- Cols numbers = (size --> size * 2 - 1)

### Example of "2" toggle:

### Example of "4" toggle:

## More examples:

```python
puzzle = [
  [ 0, 1, 0 ],
  [ 1, 0, 1 ],
  [ 1, 0, 1 ]
];
solution = find_solution(puzzle)
print(solution);
> [0, 4]
```
let's try some bigger puzzles:

```python
puzzle = [
  [ 1, 0, 1, 0, 0 ],
  [ 0, 1, 0, 1, 1 ],
  [ 0, 1, 0, 1, 1 ],
  [ 0, 1, 0, 1, 1 ],
  [ 1, 0, 1, 0, 0 ]
];
solution = find_solution(puzzle)
print(solution);
> [ 0, 5, 4, 7 ]
```

```python
puzzle = [
  [ 1, 1, 1, 0, 1, 1, 1 ],
  [ 1, 1, 1, 0, 1, 1, 1 ],
  [ 1, 1, 1, 0, 1, 1, 1 ],
  [ 0, 0, 0, 1, 0, 0, 0 ],
  [ 1, 1, 1, 0, 1, 1, 1 ],
  [ 1, 1, 1, 0, 1, 1, 1 ],
  [ 1, 1, 1, 0, 1, 1, 1 ]
];
solution = find_solution(puzzle)
print(solution);
> [ 3, 10 ]
```

There are randomized tests with puzzles of up to 100x100 in size. Have fun!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded