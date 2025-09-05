### Please also check out other katas in [Domino Tiling series](https://www.codewars.com/collections/5d19554d13dba80026a74ff5)!

---

# Task

A domino is a rectangular block with `2` units wide and `1` unit high. A domino can be placed on a grid in two ways: horizontal or vertical.

```
## or #
      #
```

You have infinitely many dominoes, and you want to fill a board that is `2*N` units wide and `5` units high:

```
<---   2N   --->
################
################
################
################
################
```

The task is to find **the number of ways** you can fill the given grid with dominoes.

Since the answer will be very large, please give your answer **modulo 12345787**.

# Examples

```python
five_by_2n(1) == 8
five_by_2n(2) == 95
five_by_2n(3) == 1183
five_by_2n(5) == 185921

five_by_2n(10) == 8228892
five_by_2n(20) == 9942990
five_by_2n(50) == 2308182
five_by_2n(100) == 334896

five_by_2n(1000) == 6032838
five_by_2n(10000) == 2392948
```

# Constraints

`1 <= N <= 10000`

All inputs are valid integers.

# Hint

The reference solution uses eleven mutual recurrence equations.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
