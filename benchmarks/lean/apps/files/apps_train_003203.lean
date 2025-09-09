-- <vc-helpers>
-- </vc-helpers>

def signed_eight_bit_number (s : String) : Bool := sorry

theorem valid_range_numbers {x : Int}
  (h : -128 ≤ x ∧ x ≤ 127) :
  signed_eight_bit_number (toString x) = true := sorry

theorem out_of_range_numbers {x : Int}
  (h : x < -128 ∨ x > 127) : 
  signed_eight_bit_number (toString x) = false := sorry

theorem non_numeric_strings {s : String}
  (h : ¬s.all (fun c => c.isDigit ∨ c = '-')) :
  signed_eight_bit_number s = false := sorry

theorem no_whitespace_prefix {x : Int} 
  (h : -128 ≤ x ∧ x ≤ 127) :
  signed_eight_bit_number (" " ++ toString x) = false := sorry

theorem no_whitespace_suffix {x : Int}
  (h : -128 ≤ x ∧ x ≤ 127) :
  signed_eight_bit_number (toString x ++ " ") = false := sorry

theorem no_whitespace_both {x : Int}
  (h : -128 ≤ x ∧ x ≤ 127) :
  signed_eight_bit_number (" " ++ toString x ++ " ") = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval signed_eight_bit_number "0"

/-
info: True
-/
-- #guard_msgs in
-- #eval signed_eight_bit_number "127"

/-
info: True
-/
-- #guard_msgs in
-- #eval signed_eight_bit_number "-128"

/-
info: False
-/
-- #guard_msgs in
-- #eval signed_eight_bit_number "128"

/-
info: False
-/
-- #guard_msgs in
-- #eval signed_eight_bit_number " 1"

-- Apps difficulty: introductory
-- Assurance level: unguarded