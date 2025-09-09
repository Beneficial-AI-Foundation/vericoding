-- <vc-helpers>
-- </vc-helpers>

def find_num (n : Nat) : Nat := sorry

theorem find_num_non_negative (n : Nat) (h : n > 0) :
  find_num n ≥ 0 := sorry

theorem find_num_unique {n : Nat} (h : n > 0) :
  ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → i ≠ j → find_num i ≠ find_num j := sorry

theorem find_num_upper_bound (n : Nat) (h : n > 0) :
  find_num n < 10000 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_num 1

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_num 5

/-
info: 22
-/
-- #guard_msgs in
-- #eval find_num 11

-- Apps difficulty: introductory
-- Assurance level: unguarded