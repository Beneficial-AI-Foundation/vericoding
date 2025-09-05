Once you complete this kata, there is a [15x15 Version](http://www.codewars.com/kata/15x15-nonogram-solver) that you can try.
And once you complete that, you can do the [Multisize Version](https://www.codewars.com/kata/5a5519858803853691000069) which goes up to 50x50.

# Description

For this kata, you will be making a Nonogram solver. :)

If you don't know what Nonograms are, you can [look at some instructions](https://www.puzzle-nonograms.com/faq.php) and also [try out some Nonograms here.](https://www.puzzle-nonograms.com/)

For this kata, you will only have to solve 5x5 Nonograms. :)

# Instructions

You need to complete the Nonogram class and the solve method:
```python
class Nonogram:

    def __init__(self, clues):
        pass

    def solve(self):
        pass
```

You will be given the clues and you should return the solved puzzle. All the puzzles will be solveable so you will not need to worry about that.

```if:python
The clues will be a tuple of the horizontal clues, then the vertical clues, which will contain the individual clues. For example, for the Nonogram:
```

```if:java
The clues will be a three dimensional array of the horizontal clues, then the vertical clues, which will contain the individual clues. For example, for the Nonogram:
```

```
    |   |   | 1 |   |   |
    | 1 |   | 1 |   |   |
    | 1 | 4 | 1 | 3 | 1 |
-------------------------
  1 |   |   |   |   |   |
-------------------------
  2 |   |   |   |   |   |
-------------------------
  3 |   |   |   |   |   |
-------------------------
2 1 |   |   |   |   |   |
-------------------------
  4 |   |   |   |   |   |
-------------------------
```
The clues are on the top and the left of the puzzle, so in this case:
```if:python
The horizontal clues are: `((1, 1), (4,), (1, 1, 1), (3,), (1,))`, and the vertical clues are: `((1,), (2,), (3,), (2, 1), (4,))`. The horizontal clues are given from left to right. If there is more than one clue for the same column, the upper clue is given first. The vertical clues are given from top to bottom. If there is more than one clue for the same row, the leftmost clue is given first.

Therefore, the clue given to the `__init__` method would be `(((1, 1), (4,), (1, 1, 1), (3,), (1,)), ((1,), (2,), (3,), (2, 1), (4,)))`. You are given the horizontal clues first then the vertical clues second.

```

```if:java
The horizontal clues are: `{{1, 1}, {4}, {1, 1, 1}, {3}, {1}}`, and the vertical clues are: `{{1}, {2}, {3}, {2, 1}, {4}}`. The horizontal clues are given from left to right. If there is more than one clue for the same column, the upper clue is given first. The vertical clues are given from top to bottom. If there is more than one clue for the same row, the leftmost clue is given first.

Therefore, the clue given to the `solve` method would be `{{{1, 1}, {4}, {1, 1, 1}, {3}, {1}},
                    {{1}, {2}, {3}, {2, 1}, {4}}}`. You are given the horizontal clues first then the vertical clues second.

```

```if:python
You should return a tuple of the rows as your answer. In this case, the solved Nonogram looks like:

```
```if:java
You should return a two-dimensional array as your answer. In this case, the solved Nonogram looks like:

```

```
    |   |   | 1 |   |   |
    | 1 |   | 1 |   |   |
    | 1 | 4 | 1 | 3 | 1 |
-------------------------
  1 |   |   | # |   |   |
-------------------------
  2 | # | # |   |   |   |
-------------------------
  3 |   | # | # | # |   |
-------------------------
2 1 | # | # |   | # |   |
-------------------------
  4 |   | # | # | # | # |
-------------------------
```

```if:python
In the tuple, you should use 0 for a unfilled square and 1 for a filled square. Therefore, in this case, you should return:
~~~
((0, 0, 1, 0, 0),
 (1, 1, 0, 0, 0),
 (0, 1, 1, 1, 0),
 (1, 1, 0, 1, 0),
 (0, 1, 1, 1, 1))
~~~

```

```if:java
In the two-dimensional array, you should use 0 for a unfilled square and 1 for a filled square. Therefore, in this case, you should return:
~~~
{{0, 0, 1, 0, 0},
 {1, 1, 0, 0, 0},
 {0, 1, 1, 1, 0},
 {1, 1, 0, 1, 0},
 {0, 1, 1, 1, 1}}
~~~

```
Good Luck!!

If there is anything that is unclear or confusing, just let me know :)

def find_min_index (lst : List Int) : Int := sorry
def find_max_index (lst : List Int) : Int := sorry

def find_second_max (lst : List Int) : Option Int := sorry

def minimum (lst : List Int) : Option Int := lst.foldl (fun min x => match min with 
  | none => some x
  | some m => if x < m then some x else some m) none

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
