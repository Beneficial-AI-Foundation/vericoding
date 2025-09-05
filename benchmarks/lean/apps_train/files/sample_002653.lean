You're familiar with [list slicing](https://docs.python.org/3/library/functions.html#slice) in Python and know, for example, that:

```python
>>> ages = [12, 14, 63, 72, 55, 24]
>>> ages[2:4]
[63, 72]
>>> ages[2:]
[63, 72, 55, 24]
>>> ages[:3]
[12, 14, 63]
```

write a function `inverse_slice()` that takes three arguments: a list `items`, an integer `a` and an integer `b`. The function should return a new list with the slice specified by `items[a:b]` _excluded_. For example:

```python
>>>inverse_slice([12, 14, 63, 72, 55, 24], 2, 4)
[12, 14, 55, 24]
```

The input will always be a valid list, `a` and `b` will always be different integers equal to or greater than zero, but they _may_ be zero or be larger than the length of the list.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
