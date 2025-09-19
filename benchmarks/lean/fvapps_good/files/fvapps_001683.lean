-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_pins (pin : String) : List String := sorry

def is_digit (c : Char) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pin_length_matches_input (pin : String) (h : ∀ c ∈ pin.data, is_digit c) :
  ∀ result ∈ get_pins pin, result.length = pin.length := sorry

theorem results_are_digits (pin : String) (h : ∀ c ∈ pin.data, is_digit c) :
  ∀ result ∈ get_pins pin, ∀ c ∈ result.data, is_digit c := sorry

theorem input_digit_in_possibilities (d : Char) (h : is_digit d) :
  let pin := String.mk [d]
  pin ∈ get_pins pin := sorry

theorem no_duplicates (pin : String) (h : ∀ c ∈ pin.data, is_digit c) :
  let results := get_pins pin
  ∀ x ∈ results, ∀ y ∈ results, x = y → x.data = y.data := sorry
-- </vc-theorems>