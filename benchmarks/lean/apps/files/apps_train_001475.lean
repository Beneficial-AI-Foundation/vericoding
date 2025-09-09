-- <vc-helpers>
-- </vc-helpers>

def print_pattern (n: Nat) : List String := sorry

theorem print_pattern_basic_2 : 
  print_pattern 2 = ["1", "32"] := sorry

theorem print_pattern_basic_3 :
  print_pattern 3 = ["1", "32", "654"] := sorry

theorem print_pattern_basic_4 :
  print_pattern 4 = ["1", "32", "654", "10987"] := sorry

theorem print_pattern_zero :
  print_pattern 0 = [] := sorry

theorem print_pattern_one :
  print_pattern 1 = ["1"] := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval print_pattern 2

/-
info: expected2
-/
-- #guard_msgs in
-- #eval print_pattern 3

/-
info: expected3
-/
-- #guard_msgs in
-- #eval print_pattern 4

-- Apps difficulty: interview
-- Assurance level: unguarded