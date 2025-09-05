There are two lists of different length. The first one consists of keys, the second one consists of values. Write a function ```createDict(keys, values)``` that returns a dictionary created from keys and values. If there are not enough values, the rest of keys should have a ```None``` value. If there not enough keys, just ignore the rest of values.

Example 1:
```python
keys = ['a', 'b', 'c', 'd']
values = [1, 2, 3]
createDict(keys, values) # returns {'a': 1, 'b': 2, 'c': 3, 'd': None}
```

Example 2:
```python
keys = ['a', 'b', 'c']
values = [1, 2, 3, 4]
createDict(keys, values) # returns {'a': 1, 'b': 2, 'c': 3}
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
