-- <vc-helpers>
-- </vc-helpers>

def disarium_number (n : Nat) : String := sorry

def digitSum (n : Nat) : Nat := sorry

theorem disarium_output_format (n : Nat) (h : n > 0 ∧ n ≤ 10000) :
  (disarium_number n = "Disarium !!") ∨ (disarium_number n = "Not !!") := sorry

theorem disarium_property (n : Nat) (h : n > 0 ∧ n ≤ 10000) :
  disarium_number n = "Disarium !!" ↔ digitSum n = n := sorry

theorem known_disarium_numbers :
  disarium_number 1 = "Disarium !!" ∧
  disarium_number 2 = "Disarium !!" ∧
  disarium_number 3 = "Disarium !!" ∧
  disarium_number 4 = "Disarium !!" ∧
  disarium_number 5 = "Disarium !!" ∧
  disarium_number 6 = "Disarium !!" ∧
  disarium_number 7 = "Disarium !!" ∧
  disarium_number 8 = "Disarium !!" ∧
  disarium_number 9 = "Disarium !!" ∧
  disarium_number 89 = "Disarium !!" ∧
  disarium_number 135 = "Disarium !!" ∧
  disarium_number 175 = "Disarium !!" ∧
  disarium_number 518 = "Disarium !!" ∧
  disarium_number 598 = "Disarium !!" := sorry

/-
info: 'Not !!'
-/
-- #guard_msgs in
-- #eval disarium_number 1024

/-
info: 'Disarium !!'
-/
-- #guard_msgs in
-- #eval disarium_number 1306

/-
info: 'Not !!'
-/
-- #guard_msgs in
-- #eval disarium_number 1999

-- Apps difficulty: introductory
-- Assurance level: unguarded