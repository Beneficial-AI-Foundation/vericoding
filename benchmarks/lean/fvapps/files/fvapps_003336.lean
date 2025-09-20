-- <vc-preamble>
def isValidInput (x : String) : Bool :=
  x = "goodpresent" ∨ x = "crap" ∨ x = "empty" ∨ x = "bang" ∨ x = "badpresent" ∨ x = "dog"
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def present (x : String) (y : Int) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem present_goodpresent_length (y : Int) :
  String.length (present "goodpresent" y) = String.length "goodpresent" :=
sorry

theorem present_crap_fixed (y : Int) :
  present "crap" y = "acpr" :=
sorry

theorem present_empty_fixed (y : Int) :
  present "empty" y = "empty" :=
sorry

theorem present_badpresent_fixed (y : Int) :
  present "badpresent" y = "Take this back!" :=
sorry

theorem present_dog_contains_number (y : Int) :
  ∃ s : String, s = toString y ∧ present "dog" y = s :=
sorry

theorem present_invalid_input (x : String) (h : ¬isValidInput x) :
  ∃ err, present x 0 = err :=
sorry
-- </vc-theorems>