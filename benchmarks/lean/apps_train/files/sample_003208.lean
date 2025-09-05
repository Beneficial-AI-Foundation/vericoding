The squarefree part of a positive integer is the largest divisor of that integer which itself has no square factors (other than 1). For example, the squareefree part of 12 is 6, since the only larger divisor is 12, and 12 has a square factor (namely, 4).

Your challenge, should you choose to accept it, is to implement a `squareFreePart` function which accepts a number `n` and returns the squarefree part of `n`. 

In the case that `n = 1`, your function should return 1. Also, if the input doesn't make sense (e.g. if it is not a positive integer), the function should return `null/None`. 

Here are some examples:

```python
square_free_part(2) # returns 2
square_free_part(4) # returns 2
square_free_part(24) # returns 6, since any larger divisor is divisible by 4, which is a square
square_free_part("hi") # returns None
square_free_part(0) # returns None
```

Good luck!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded