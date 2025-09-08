/-
Write a function that takes as its parameters *one or more numbers which are the diameters of circles.* 

The function should return the *total area of all the circles*, rounded to the nearest integer in a string that says "We have this much circle: xyz". 

You don't know how many circles you will be given, but you can assume it will be at least one.

So: 
```python
sum_circles(2) == "We have this much circle: 3"
sum_circles(2, 3, 4) == "We have this much circle: 23"
```

Translations and comments (and upvotes!) welcome!
-/

-- <vc-helpers>
-- </vc-helpers>

def listOfNumsInBounds (start : Nat) (end_ : Nat) : List Nat := sorry

theorem listOfNumsInBounds_length (start : Nat) (end_ : Nat) :
  (listOfNumsInBounds start end_).length = end_ - start + 1 := sorry

theorem listOfNumsInBounds_starts_with_start (start : Nat) (end_ : Nat) :
  start ≤ end_ →
  (listOfNumsInBounds start end_).head! = start := sorry

theorem listOfNumsInBounds_within_bounds (start : Nat) (end_ : Nat) (n : Nat) :
  start ≤ end_ →
  n ∈ (listOfNumsInBounds start end_) →
  start ≤ n ∧ n ≤ end_ := sorry

theorem listOfNumsInBounds_all_included (start : Nat) (end_ : Nat) (n : Nat) :
  start ≤ end_ →
  start ≤ n →
  n ≤ end_ →
  n ∈ (listOfNumsInBounds start end_) := sorry

/-
info: 'We have this much circle: 3'
-/
-- #guard_msgs in
-- #eval sum_circles 2

/-
info: 'We have this much circle: 23'
-/
-- #guard_msgs in
-- #eval sum_circles 2 3 4

/-
info: 'We have this much circle: 2040'
-/
-- #guard_msgs in
-- #eval sum_circles 48 7 8 9 10

-- Apps difficulty: introductory
-- Assurance level: unguarded