Two numbers are **relatively prime** if their greatest common factor is 1; in other words: if they cannot be divided by any other common numbers than 1.

`13, 16, 9, 5, and 119` are all relatively prime because they share no common factors, except for 1. To see this, I will show their factorizations:
```python
 13: 13
 16: 2 * 2 * 2 * 2
  9: 3 * 3
  5: 5
119: 17 * 7
```

Complete the function that takes 2 arguments: a number (`n`), and a list of numbers (`arr`). The function should return a list of all the numbers in `arr` that are relatively prime to `n`. All numbers in will be positive integers.

## Examples

```python
relatively_prime(8, [1, 2, 3, 4, 5, 6, 7])
>> [1, 3, 5, 7]

relatively_prime(15, [72, 27, 32, 61, 77, 11, 40])
>> [32, 61, 77, 11]

relatively_prime(210, [15, 100, 2222222, 6, 4, 12369, 99])
>> []
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded