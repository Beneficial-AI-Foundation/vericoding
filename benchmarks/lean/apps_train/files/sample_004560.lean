Classy Extensions
Classy Extensions, this kata is mainly aimed at the new JS ES6 Update introducing extends keyword. You will be preloaded with the Animal class, so you should only edit the Cat class.

Task
Your task is to complete the Cat class which Extends Animal and replace the speak method to return the cats name + meows.
e.g. 'Mr Whiskers meows.'

The name attribute is passed with this.name (JS), @name (Ruby) or self.name (Python).

Reference: [JS](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Classes), [Ruby](http://rubylearning.com/satishtalim/ruby_inheritance.html), [Python](https://docs.python.org/2/tutorial/classes.html#inheritance).

def Animal.name (a : Animal) : String :=
  match a with
  | mk n => n

def Animal.speak (a : Animal) : String := sorry

inductive Cat where
  | mk (name : String)

def Cat.name (c : Cat) : String :=
  match c with
  | mk n => n

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded