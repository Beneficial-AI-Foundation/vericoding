def is_dd (n : Nat) : Bool := sorry 

def countDigit (n : Nat) (d : Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def digits (n : Nat) : List Nat := sorry 

theorem dd_characterization (n : Nat) :
  is_dd n = (∃ d : Nat, 1 ≤ d ∧ d ≤ 9 ∧ countDigit n d = d) := sorry

theorem zero_not_counted (n : Nat) :
  (∀ d : Nat, d ≠ 0 → countDigit n d ≠ d) → 
  is_dd n = false := sorry

theorem count_digit_bounds (n d : Nat) :
  countDigit n d ≤ (digits n).length := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_dd 664444309

/-
info: True
-/
-- #guard_msgs in
-- #eval is_dd 122

/-
info: True
-/
-- #guard_msgs in
-- #eval is_dd 30313

/-
info: False
-/
-- #guard_msgs in
-- #eval is_dd 5023011

-- Apps difficulty: introductory
-- Assurance level: unguarded