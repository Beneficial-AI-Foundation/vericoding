-- <vc-helpers>
-- </vc-helpers>

def find_number (divisors : List Nat) : Nat := sorry

def get_proper_divisors (n : Nat) : List Nat := sorry

theorem find_number_preserves_input {divisors original : List Nat} 
  (h : original = divisors) :
  original = divisors := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval find_number [2, 3]

/-
info: 8
-/
-- #guard_msgs in
-- #eval find_number [4, 2]

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_number [12, 3, 2]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible