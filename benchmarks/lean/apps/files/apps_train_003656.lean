-- <vc-helpers>
-- </vc-helpers>

def close_to_zero (input : String) : Int := sorry

def abs (n : Int) : Int := sorry

theorem close_to_zero_returns_from_input_or_zero 
  (nums : List Int) : 
  nums.isEmpty → close_to_zero (toString nums) = 0 ∧
  ¬nums.isEmpty → close_to_zero (toString nums) = 0 ∨ 
    close_to_zero (toString nums) ∈ nums := sorry

theorem empty_string_returns_zero : 
  close_to_zero "" = 0 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval close_to_zero ""

/-
info: 0
-/
-- #guard_msgs in
-- #eval close_to_zero "-1 50 -4 20 22 -7 0 10 -8"

/-
info: 17
-/
-- #guard_msgs in
-- #eval close_to_zero "28 35 -21 17 38 -17"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible