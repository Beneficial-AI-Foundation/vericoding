-- <vc-helpers>
-- </vc-helpers>

def last_two_digits_of_5powern (n : Nat) : Nat := sorry

theorem result_in_valid_range 
  (n : Nat) : 
  let result := last_two_digits_of_5powern n
  0 ≤ result ∧ result ≤ 99 := sorry

theorem matches_manual_calculation
  (n : Nat) :
  last_two_digits_of_5powern n = (5^n : Nat) % 100 := sorry

theorem negative_input_undefined
  (n : Int) :
  n < 0 → last_two_digits_of_5powern n.toNat = last_two_digits_of_5powern 0 := sorry

/-
info: 25
-/
-- #guard_msgs in
-- #eval last_two_digits_of_5powern 2

/-
info: 25
-/
-- #guard_msgs in
-- #eval last_two_digits_of_5powern 3

/-
info: 25
-/
-- #guard_msgs in
-- #eval last_two_digits_of_5powern 4

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible