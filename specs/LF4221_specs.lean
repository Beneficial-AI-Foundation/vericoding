-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BUTTONS : List String :=
sorry

def presses (s : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem keypad_chars_valid (s : String) :
  (∀ c ∈ s.data, ∃ button ∈ BUTTONS, c ∈ button.data) →
  presses s ≥ s.length :=
sorry

theorem case_insensitive (button : String) :
  button ∈ BUTTONS →
  presses button.toUpper = presses button.toLower :=
sorry

theorem numeric_and_space_presses (s : String) :
  (∀ c ∈ s.data, c ∈ [' ', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9']) →
  presses s ≥ s.length :=
sorry
-- </vc-theorems>