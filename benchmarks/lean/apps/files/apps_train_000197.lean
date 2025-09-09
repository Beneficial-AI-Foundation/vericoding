-- <vc-helpers>
-- </vc-helpers>

def num_unique_bst (n : Nat) : Nat := sorry

theorem num_unique_bst_base_cases : 
  num_unique_bst 0 = 1 ∧ 
  num_unique_bst 1 = 1 ∧ 
  num_unique_bst 2 = 2 := sorry

theorem num_unique_bst_positive (n : Nat) : 
  num_unique_bst n > 0 := sorry

theorem num_unique_bst_increasing (n : Nat) :
  n ≥ 2 → num_unique_bst n > num_unique_bst (n-1) := sorry

theorem num_unique_bst_deterministic (n : Nat) :
  num_unique_bst n = num_unique_bst n := sorry

theorem num_unique_bst_known_values :
  num_unique_bst 0 = 1 ∧
  num_unique_bst 1 = 1 ∧
  num_unique_bst 2 = 2 ∧
  num_unique_bst 3 = 5 ∧
  num_unique_bst 4 = 14 ∧
  num_unique_bst 5 = 42 ∧
  num_unique_bst 6 = 132 ∧
  num_unique_bst 7 = 429 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval num_unique_bst 3

/-
info: 14
-/
-- #guard_msgs in
-- #eval num_unique_bst 4

/-
info: 42
-/
-- #guard_msgs in
-- #eval num_unique_bst 5

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible