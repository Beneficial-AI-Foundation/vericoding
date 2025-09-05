Final kata of the series (highly recommended to compute [layers](https://www.codewars.com/kata/progressive-spiral-number-position/) and [branch](https://www.codewars.com/kata/progressive-spiral-number-branch/) first to get a good idea), this is a blatant ripoff of [the one offered on AoC](http://adventofcode.com/2017/day/3).

Given a number, return the Manhattan distance considering the core of the spiral (the `1` cell) as 0 and counting each step up, right, down or left to reach a given cell.

For example, using our beloved 5x5 square:

```
17 16 15 14 13    4 3 2 3 4
18 05 04 03 12    3 2 1 2 3
19 06 01 02 11 => 2 1 0 1 2
20 07 08 09 10    3 2 1 2 3
21 22 23 24 25    4 3 2 3 4
```

And thus your code should behave like this:

```python
distance(1) == 0
distance(5) == 2
distance(25) == 4
distance(30) == 5
distance(50) == 7
```

Just be ready for larger numbers, as usual always positive.

*[Dedicated to [swiftest learner I met in a long while](https://www.codewars.com/users/irbekrm/)]*

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible