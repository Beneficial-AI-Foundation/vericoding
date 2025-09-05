Finish the solution so that it sorts the passed in array of numbers. If the function passes in an empty array or null/nil value then it should return an empty array.

For example:

```python
solution([1,2,3,10,5]) # should return [1,2,3,5,10]
solution(None) # should return []
```

```Hakell
sortNumbers [1, 2, 10, 50, 5] = Just [1, 2, 5, 10, 50]
sortNumbers [] = Nothing
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded