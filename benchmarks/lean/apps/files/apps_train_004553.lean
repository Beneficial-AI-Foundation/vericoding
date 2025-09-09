def get_num (n : Nat) : Nat := sorry

def countDigits (n : Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def natToString (n : Nat) : String := sorry

theorem get_num_zero : get_num 0 = 1 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval get_num 123

/-
info: 4
-/
-- #guard_msgs in
-- #eval get_num 6609

/-
info: 8
-/
-- #guard_msgs in
-- #eval get_num 8888

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible