-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BUTTONS : List String := sorry
def presses (s : String) : Nat := sorry

/- For any string made up of valid keypad characters, the number of presses
    should be at least the length of the string, and each character should
    be present in one of the buttons -/
-- </vc-definitions>

-- <vc-theorems>
theorem keypad_chars_valid (s : String) :
  (∀ c ∈ s.data, ∃ button ∈ BUTTONS, c ∈ button.data) →
  presses s ≥ s.length := sorry
-- </vc-theorems>