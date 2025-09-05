A nested list (or *array* in JavaScript) is a list that apears as a value inside another list, 
```python
[item, item, [item, item], item]
```
in the above list, [item, item] is a nested list.  

Your goal is to write a function that determines the depth of the deepest nested list within a given list.  
return 1 if there are no nested lists.
The list passed to your function can contain any data types.  

A few examples:

```python
list_depth([True])
return 1

list_depth([])
return 1

list_depth([2, "yes", [True, False]])
return 2

list_depth([1, [2, [3, [4, [5, [6], 5], 4], 3], 2], 1])
return 6

list_depth([2.0, [2, 0], 3.7, [3, 7], 6.7, [6, 7]])
return 2
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded