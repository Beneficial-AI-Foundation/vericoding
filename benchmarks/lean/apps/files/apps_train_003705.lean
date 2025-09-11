-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validate (message : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem validate_valid_messages (message : String) : 
  (∃ digits1 digits2 digits3 word digits4 digits5 digits6 digits7 : String,
    message = s!"MDZHB {digits1} {digits2} {word} {digits4} {digits5} {digits6} {digits7}" ∧
    digits1.length = 2 ∧
    digits2.length = 3 ∧
    word.all Char.isUpper ∧
    digits4.length = 2 ∧
    digits5.length = 2 ∧
    digits6.length = 2 ∧
    digits7.length = 2 ∧
    digits1.all Char.isDigit ∧
    digits2.all Char.isDigit ∧
    digits4.all Char.isDigit ∧
    digits5.all Char.isDigit ∧
    digits6.all Char.isDigit ∧
    digits7.all Char.isDigit) →
  validate message = true :=
sorry

theorem validate_invalid_messages (message : String) :
  (¬∃ digits1 digits2 digits3 word digits4 digits5 digits6 digits7 : String,
    message = s!"MDZHB {digits1} {digits2} {word} {digits4} {digits5} {digits6} {digits7}" ∧
    digits1.length = 2 ∧
    digits2.length = 3 ∧
    word.all Char.isUpper ∧
    digits4.length = 2 ∧
    digits5.length = 2 ∧
    digits6.length = 2 ∧
    digits7.length = 2 ∧
    digits1.all Char.isDigit ∧
    digits2.all Char.isDigit ∧
    digits4.all Char.isDigit ∧
    digits5.all Char.isDigit ∧
    digits6.all Char.isDigit ∧
    digits7.all Char.isDigit) →
  validate message = false :=
sorry

theorem validate_correct_pattern (message : String) :
  validate message = true →
  ∃ digits1 digits2 digits3 word digits4 digits5 digits6 digits7 : String,
    message = s!"MDZHB {digits1} {digits2} {word} {digits4} {digits5} {digits6} {digits7}" ∧
    digits1.length = 2 ∧
    digits2.length = 3 ∧
    word.all Char.isUpper ∧
    digits4.length = 2 ∧
    digits5.length = 2 ∧
    digits6.length = 2 ∧
    digits7.length = 2 ∧
    digits1.all Char.isDigit ∧
    digits2.all Char.isDigit ∧
    digits4.all Char.isDigit ∧
    digits5.all Char.isDigit ∧
    digits6.all Char.isDigit ∧
    digits7.all Char.isDigit :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval validate "MDZHB 85 596 KLASA 81 00 02 91"

/-
info: False
-/
-- #guard_msgs in
-- #eval validate "MDZHV 60 130 VATRUKH 58 89 54 54"

/-
info: False
-/
-- #guard_msgs in
-- #eval validate "MDZHB 12 733 EDIN ENIE 67 79 66 32"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded