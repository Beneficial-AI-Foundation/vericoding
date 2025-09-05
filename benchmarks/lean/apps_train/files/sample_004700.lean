Your task is to implement a function that takes one or more dictionaries and combines them in one result dictionary.

The keys in the given dictionaries can overlap. In that case you should combine all source values in an array. Duplicate values should be preserved.

Here is an example:
```cs
var source1 = new Dictionary{{"A", 1}, {"B", 2}}; 
var source2 = new Dictionary{{"A", 3}};

Dictionary result = DictionaryMerger.Merge(source1, source2);
// result should have this content: {{"A", [1, 3]}, {"B", [2]}}

```
```python
source1 = {"A": 1, "B": 2} 
source2 = {"A": 3}

result = merge(source1, source2);
// result should have this content: {"A": [1, 3]}, "B": [2]}

```

You can assume that only valid dictionaries are passed to your function.
The number of given dictionaries might be large. So take care about performance.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
