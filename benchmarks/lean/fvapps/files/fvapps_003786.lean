-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_happy (n : Nat) : Bool := sorry

def sum_of_squares_digits (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem happy_number_is_bool (n : Nat) : 
  n > 0 → is_happy n = true ∨ is_happy n = false := sorry 

theorem happy_number_squares_property (n : Nat) : 
  n > 0 → is_happy n = true → is_happy (sum_of_squares_digits n) = true := sorry

theorem happy_number_squares_property_false (n : Nat) :
  n > 0 → is_happy n = false → is_happy (sum_of_squares_digits n) = false := sorry

theorem known_happy_numbers :
  is_happy 1 = true ∧ 
  is_happy 7 = true ∧
  is_happy 10 = true ∧
  is_happy 13 = true ∧ 
  is_happy 19 = true ∧
  is_happy 23 = true ∧
  is_happy 28 = true ∧
  is_happy 31 = true := sorry

theorem happy_number_terminates (n : Nat) :
  n > 0 → ∃ result, is_happy n = result := sorry
-- </vc-theorems>