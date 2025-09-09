-- <vc-helpers>
-- </vc-helpers>

def look_and_say_and_sum (n : Nat) : Nat := sorry

theorem look_and_say_first_value :
  look_and_say_and_sum 1 = 1 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval look_and_say_and_sum 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval look_and_say_and_sum 2

/-
info: 3
-/
-- #guard_msgs in
-- #eval look_and_say_and_sum 3

/-
info: 5
-/
-- #guard_msgs in
-- #eval look_and_say_and_sum 4

/-
info: 8
-/
-- #guard_msgs in
-- #eval look_and_say_and_sum 5

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible