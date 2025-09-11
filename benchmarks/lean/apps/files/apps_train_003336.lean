-- <vc-preamble>
def present (x : String) (y : Int) : String := sorry

theorem present_goodpresent_length (y : Int) : 
  String.length (present "goodpresent" y) = String.length "goodpresent" := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidInput (x : String) : Bool :=
  x = "goodpresent" ∨ x = "crap" ∨ x = "empty" ∨ x = "bang" ∨ x = "badpresent" ∨ x = "dog"
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded