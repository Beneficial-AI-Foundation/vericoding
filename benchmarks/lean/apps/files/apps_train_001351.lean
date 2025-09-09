-- <vc-helpers>
-- </vc-helpers>

def count_binary_additions (s1 s2 : String) : Nat := sorry

theorem zeros_add_no_carry : 
  count_binary_additions "0" "0" = 0 := sorry

theorem one_zero_no_carry :
  count_binary_additions "1" "0" = 0 := sorry 

theorem zero_one_one_carry :
  count_binary_additions "0" "1" = 1 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_binary_additions "100010" "0"

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_binary_additions "0" "100010"

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_binary_additions "11100" "1010"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible