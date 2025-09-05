The built-in print function for Python class instances is not very entertaining.

In this Kata, we will implement a function ```show_me(instname)``` that takes an instance name as parameter and returns the string "Hi, I'm one of those (classname)s! Have a look at my (attrs).", where (classname) is the class name and (attrs) are the class's attributes. If (attrs) contains only one element, just write it. For more than one element (e.g. a, b, c), it should list all elements sorted by name in ascending order (e.g. "...look at my a, b and c").

Example:
For an instance ```porsche = Vehicle(2, 4, 'gas')``` of the class
```
class Vehicle:
  def __init__(self, seats, wheels, engine):
    self.seats = seats
    self.wheels = wheels
    self.engine = engine
```
the function call ```show_me(porsche)``` should return the string 'Hi, I'm one of those Vehicles! Have a look at my engine, seats and wheels.'

Hints:
For simplicity we assume that the parameter "instname" is always a class instance.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
