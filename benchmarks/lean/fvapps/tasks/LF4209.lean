-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validatePin (pin : String) : Bool := sorry

theorem validate_pin_length (pin : String) :
  let len := pin.length
  (len ≠ 4 ∧ len ≠ 6) → validatePin pin = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem validate_pin_digits (pin : String) :
  let len := pin.length
  (len = 4 ∨ len = 6) → 
  pin.all Char.isDigit → validatePin pin = true := sorry

theorem validate_pin_nondigits (pin : String) :
  let len := pin.length
  (len = 4 ∨ len = 6) →
  (∃ c ∈ pin.data, ¬c.isDigit) → validatePin pin = false := sorry

theorem validate_pin_abs_number (n : Int) :
  let pin := toString (Int.natAbs n)
  let len := pin.length
  (len = 4 ∨ len = 6) → validatePin pin = true := sorry

theorem validate_pin_non_numeric_chars (pin : String) :
  (∀ c ∈ pin.data, ¬c.isDigit) → validatePin pin = false := sorry
-- </vc-theorems>