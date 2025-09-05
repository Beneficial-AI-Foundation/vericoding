### Task
The __dot product__ is usually encountered in linear algebra or scientific computing. It's also called __scalar product__ or __inner product__ sometimes:

> In mathematics, the __dot product__, or __scalar product__ (or sometimes __inner product__ in the context of Euclidean space), is an algebraic operation that takes two equal-length sequences of numbers (usually coordinate vectors) and returns a single number. [Wikipedia](https://en.wikipedia.org/w/index.php?title=Dot_product&oldid=629717691)

In our case, we define the dot product algebraically for two vectors `a = [a1, a2, …, an]`, `b = [b1, b2, …, bn]` as 

    dot a b = a1 * b1 + a2 * b2 + … + an * bn.
Your task is to find permutations of `a` and `b`, such that `dot a b` is minimal, and return that value. For example, the dot product of `[1,2,3]` and `[4,0,1]` is minimal if we switch `0` and `1` in the second vector.

### Examples
```python
min_dot([1,2,3,4,5], [0,1,1,1,0] ) = 6
min_dot([1,2,3,4,5], [0,0,1,1,-4]) = -17
min_dot([1,3,5]    , [4,-2,1]    ) = -3
```

### Remarks
If the list or array is empty, `minDot` should return 0. All arrays or lists will have the same length. Also, for the dynamically typed languages, all inputs will be valid lists or arrays, you don't need to check for `undefined`, `null` etc.

Note: This kata is inspired by [GCJ 2008](https://code.google.com/codejam/contest/32016/dashboard#s=p0).

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
