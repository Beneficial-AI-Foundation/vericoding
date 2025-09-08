/-
Your colleagues have been good enough(?) to buy you a birthday gift. Even though it is your birthday and not theirs, they have decided to play pass the parcel with it so that everyone has an even chance of winning. There are multiple presents, and you will receive one, but not all are nice... One even explodes and covers you in soil... strange office. To make up for this one present is a dog! Happy days! (do not buy dogs as presents, and if you do, never wrap them).

Depending on the number of passes in the game (y), and the present you unwrap (x), return as follows:

x == goodpresent --> return x with num of passes added to each charCode (turn to charCode, add y to each, turn back)
x == crap || x == empty --> return string sorted alphabetically
x == bang --> return string turned to char codes, each code reduced by number of passes and summed to a single figure
x == badpresent --> return 'Take this back!'
x == dog, return 'pass out from excitement y times' (where y is the value given for y).
-/

def present (x : String) (y : Int) : String := sorry

theorem present_goodpresent_length (y : Int) : 
  String.length (present "goodpresent" y) = String.length "goodpresent" := sorry

-- <vc-helpers>
-- </vc-helpers>

def isValidInput (x : String) : Bool :=
  x = "goodpresent" ∨ x = "crap" ∨ x = "empty" ∨ x = "bang" ∨ x = "badpresent" ∨ x = "dog"

theorem present_crap_fixed (y : Int) :
  present "crap" y = "acpr" := sorry

theorem present_empty_fixed (y : Int) :
  present "empty" y = "empty" := sorry

theorem present_badpresent_fixed (y : Int) :
  present "badpresent" y = "Take this back!" := sorry

theorem present_dog_contains_number (y : Int) :
  ∃ s : String, s = toString y ∧ present "dog" y = s := sorry

theorem present_invalid_input (x : String) (h : ¬isValidInput x) :
  ∃ err, present x 0 = err := sorry

/-
info: 'Take this back!'
-/
-- #guard_msgs in
-- #eval present "badpresent" 3

/-
info: 'pxxmy{n|nw}'
-/
-- #guard_msgs in
-- #eval present "goodpresent" 9

/-
info: 'pass out from excitement 23 times'
-/
-- #guard_msgs in
-- #eval present "dog" 23

-- Apps difficulty: introductory
-- Assurance level: unguarded