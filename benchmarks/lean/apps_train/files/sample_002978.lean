Write a function
```python
alternate_sort(l)
```
that combines the elements of an array by sorting the elements ascending by their **absolute value** and outputs negative and non-negative integers alternatingly (starting with the negative value, if any).

E.g.
```python
alternate_sort([5, -42, 2, -3, -4, 8, -9,]) == [-3, 2, -4, 5, -9, 8, -42]
alternate_sort([5, -42, 2, -3, -4, 8, 9]) == [-3, 2, -4, 5, -42, 8, 9]
alternate_sort([5, 2, -3, -4, 8, -9]) == [-3, 2, -4, 5, -9, 8]
alternate_sort([5, 2, 9, 3, 8, 4]) == [2, 3, 4, 5, 8, 9]
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible