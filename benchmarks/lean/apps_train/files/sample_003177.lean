Create a function which checks a number for three different properties.

- is the number prime?
- is the number even?
- is the number a multiple of 10?

Each should return either true or false, which should be given as an array. Remark: The Haskell variant uses `data Property`.

### Examples
```python
number_property(7)  # ==> [true,  false, false] 
number_property(10) # ==> [false, true,  true] 
```
The number will always be an integer, either positive or negative. Note that negative numbers cannot be primes, but they can be multiples of 10:

```python
number_property(-7)  # ==> [false, false, false] 
number_property(-10) # ==> [false, true,  true] 
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded