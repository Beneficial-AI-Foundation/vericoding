-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: set(['2', '4', '5', '6', '8'])
-/
-- #guard_msgs in
-- #eval set get_pins("5")

/-
info: set(['11', '12', '14', '21', '22', '24', '41', '42', '44'])
-/
-- #guard_msgs in
-- #eval set get_pins("11")

/-
info: set(['0', '8'])
-/
-- #guard_msgs in
-- #eval set get_pins("0")
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded