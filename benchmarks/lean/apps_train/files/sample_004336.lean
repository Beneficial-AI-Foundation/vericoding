You are given two positive integer lists with a random number of elements (1 <= n <= 100). Create a [GCD](https://en.wikipedia.org/wiki/Greatest_common_divisor) matrix and calculate the average of all values. 

Return a float value rounded to 3 decimal places. 

## Example

```
a = [1, 2, 3]
b = [4, 5, 6]

#       a =    1  2  3     b =
gcd(a, b) = [ [1, 2, 1],   # 4
              [1, 1, 1],   # 5
              [1, 2, 3] ]  # 6

average(gcd(a, b)) = 1.444
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
