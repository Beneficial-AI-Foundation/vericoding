def check_permutation_divisible_by_3 (n : Nat) : Nat := sorry

def sum_digits (n : Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def get_digits (n : Nat) : List Nat := sorry

def sort_digits (n : Nat) : Nat := sorry

theorem check_permutation_returns_binary (n : Nat) :
  check_permutation_divisible_by_3 n = 0 ∨ check_permutation_divisible_by_3 n = 1 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval check_permutation_divisible_by_3 18

/-
info: 0
-/
-- #guard_msgs in
-- #eval check_permutation_divisible_by_3 308

/-
info: 1
-/
-- #guard_msgs in
-- #eval check_permutation_divisible_by_3 123

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible