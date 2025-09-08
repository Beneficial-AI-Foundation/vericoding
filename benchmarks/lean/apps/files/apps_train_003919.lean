/-
Some new animals have arrived at the zoo. The zoo keeper is concerned that perhaps the animals do not have the right tails. To help her, you must correct the broken function to make sure that the second argument (tail), is the same as the last letter of the first argument (body) - otherwise the tail wouldn't fit!

If the tail is right return true, else return false.

The arguments will always be strings, and normal letters.
-/

-- <vc-helpers>
-- </vc-helpers>

def correctTail (body tail : String) : Bool := sorry

theorem correct_tail_when_ends_with (body tail : String) 
  (h : String.endsWith body tail = true) : 
  correctTail body tail = true := sorry

theorem correct_tail_when_not_ends_with (body tail : String)
  (h : String.endsWith body tail = false) :
  correctTail body tail = false := sorry

theorem correct_tail_single_char (body tail : String)
  (h : tail.length = 1) :
  correctTail body tail = (body.back = tail.front) := sorry

theorem correct_tail_reflexive (text : String) :
  correctTail text text = true := sorry

theorem correct_tail_empty_strings : 
  correctTail "" "" = true := sorry

theorem correct_tail_empty_tail (x : String) :
  correctTail x "" = true := sorry

theorem correct_tail_empty_body (x : String) :
  correctTail "" x = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval correct_tail "Fox" "x"

/-
info: True
-/
-- #guard_msgs in
-- #eval correct_tail "Rhino" "o"

/-
info: False
-/
-- #guard_msgs in
-- #eval correct_tail "Badger" "s"

-- Apps difficulty: introductory
-- Assurance level: unguarded