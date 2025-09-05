Create a `Vector` class with `x` and a `y` attributes that represent component magnitudes in the x and y directions.

Your vectors should handle vector additon with an `.add()` method that takes a second vector as an argument and returns a new vector equal to the sum of the vector you call `.add()` on and the vector you pass in.

For example:

```python
>>> a = Vector(3, 4)
>>> a.x
3
>>> a.y
4
>>> b = Vector(1, 2)
>>> c = a.add(b)
>>> c.x
4
>>> c.y
6
```

Adding vectors when you have their components is easy: just add the two x components together and the two y components together to get the x and y components for the vector sum.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded