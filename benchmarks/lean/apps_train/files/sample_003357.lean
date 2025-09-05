Implement a function that normalizes out of range sequence indexes (converts them to 'in range' indexes) by making them repeatedly 'loop' around the array. The function should then return the value at that index. Indexes that are not out of range should be handled normally and indexes to empty sequences should return undefined/None depending on the language.

For positive numbers that are out of range, they loop around starting at the beginning, so 

```python
norm_index_test(seq, len(seq))     # Returns first element
norm_index_test(seq, len(seq) + 1) # Returns second element
norm_index_test(seq, len(seq) + 2) # Returns third element
# And so on...
norm_index_test(seq, len(seq) * 2) # Returns first element
```

For negative numbers, they loop starting from the end, so

```python norm_index_test(seq, len(seq))
norm_index_test(seq, -1)        # Returns last element
norm_index_test(seq, -2)        # Returns second to last element
norm_index_test(seq, -3)        # Returns third to last element
# And so on...
norm_index_test(seq, -len(seq)) # Returns first element
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded