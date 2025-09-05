Given an array containing only zeros and ones, find the index of the zero that, if converted to one, will make the longest sequence of ones.

For instance, given the array:

```
[1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1]
```

replacing the zero at index 10 (counting from 0) forms a sequence of 9 ones:

```
[1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1]
                  '------------^------------'
```

Your task is to complete the function that determines where to replace a zero with a one to make the maximum length subsequence.

**Notes:**
- If there are multiple results, return the last one:

 `[1, 1, 0, 1, 1, 0, 1, 1] ==> 5`

- The array will always contain only zeros and ones.

Can you do this in one pass?

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded