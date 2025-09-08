/-
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
-/

-- <vc-helpers>
-- </vc-helpers>

def show_me {α : Type} (obj : α) : String := sorry

class SingleAttr where
  attr : String
deriving Inhabited

class TestClass where
  a : Nat 
  b : Nat
  c : Nat
deriving Inhabited

theorem single_attribute {attr_name : String} (h : attr_name ≠ "") :
  let obj := SingleAttr.mk attr_name
  let result := show_me obj
  result.contains (attr_name.get ⟨0⟩) ∧ ¬result.contains '&' := sorry

theorem multiple_attributes :
  let obj := TestClass.mk 1 2 3
  let result := show_me obj
  result.startsWith "Hi, I'm one of those TestClasss!" ∧ 
  result.contains '&' ∧
  result.contains 'a' ∧ 
  result.contains 'b' ∧
  result.contains 'c' ∧
  result.endsWith "a, b and c." := sorry

/-
info: "Hi, I'm one of those Vehicles! Have a look at my engine, seats and wheels."
-/
-- #guard_msgs in
-- #eval show_me Vehicle(2, 4, "gas")

/-
info: "Hi, I'm one of those Pets! Have a look at my name."
-/
-- #guard_msgs in
-- #eval show_me Pet("Rover")

-- Apps difficulty: introductory
-- Assurance level: unguarded