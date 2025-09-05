Write a function 
```javascript 
tripledouble(num1,num2)
```
```python
triple_double(num1, num2)
```
which takes numbers `num1` and `num2` and returns `1` if there is a straight triple of a number at any place in `num1` and also a straight double of the **same** number in `num2`.

If this isn't the case, return `0`

## Examples

```python
triple_double(451999277, 41177722899) == 1
# num1 has straight triple 999s and num2 has straight double 99s

triple_double(1222345, 12345) == 0
# num1 has straight triple 2s but num2 has only a single 2

triple_double(12345, 12345) == 0

triple_double(666789, 12345667) == 1
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded