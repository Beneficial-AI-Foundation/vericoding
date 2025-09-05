Create a class Vector that has simple (3D) vector operators.

In your class, you should support the following operations, given Vector ```a``` and Vector ```b```:

```python
a + b # returns a new Vector that is the resultant of adding them
a - b # same, but with subtraction
a == b # returns true if they have the same magnitude and direction
a.cross(b) # returns a new Vector that is the cross product of a and b
a.dot(b) # returns a number that is the dot product of a and b
a.to_tuple() # returns a tuple representation of the vector.
str(a) # returns a string representation of the vector in the form ""
a.magnitude # returns a number that is the magnitude (geometric length) of vector a.
a.x # gets x component
a.y # gets y component
a.z # gets z component
Vector([a,b,c]) # creates a new Vector from the supplied 3D array.
Vector(a,b,c) # same as above
```
The test cases will not mutate the produced Vector objects, so don't worry about that.

def Vector.toTuple (v : Vector) : Int × Int × Int := sorry
def Vector.fromList (l : List Int) : Vector := sorry

def Vector.add (v1 v2 : Vector) : Vector := sorry
def Vector.sub (v1 v2 : Vector) : Vector := sorry

def Vector.dot (v1 v2 : Vector) : Int := sorry
def Vector.cross (v1 v2 : Vector) : Vector := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
