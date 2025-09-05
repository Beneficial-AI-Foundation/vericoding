### Please also check out other katas in [Domino Tiling series](https://www.codewars.com/collections/5d19554d13dba80026a74ff5)!

---

# Task

A domino is a rectangular block with `2` units wide and `1` unit high. A domino can be placed on a grid in two ways: horizontal or vertical.

```
## or #
      #
```

You have infinitely many dominoes, and you want to fill a board that is `N` units wide and `3` units high:

```
<---   N   --->
###############
###############
###############
```

The task is to find **the number of ways** you can fill the given grid with dominoes.

# The Twist

But you quickly realize that the answer is zero for any odd `N`, because (obviously) you can't cover odd number of cells with dominoes! So you decide to introduce one **unit block** (1 unit wide and 1 unit high) to cover the final gap when needed (you don't need this block when `N` is even).

The following shows some possible tilings for `N = 5`. Note that, unlike my previous Kata, the numbers do not represent the colors (they are just for convenience). Also note that the unit block (marked as 'X') can be placed **anywhere on the board**, making the answers for odd numbers way higher than even ones.

```
11255   1122X   14456
3X267   33447   13356
34467   55667   22X77
```

Since the answer will be very large, please give your answer **modulo 12345787**.

# Examples

```python
# Even input
three_by_n(2) == 3
three_by_n(4) == 11
three_by_n(10) == 571
three_by_n(20) == 413403

# Odd input (the numbers grow much faster than even inputs)
three_by_n(1) == 2
three_by_n(3) == 18
three_by_n(5) == 106
three_by_n(11) == 11542
three_by_n(21) == 3287999

# You must handle big values
three_by_n(9999) == 6311027
three_by_n(10000) == 12003229
```

# Constraints

`1 <= N <= 10000`

All inputs are valid integers.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
