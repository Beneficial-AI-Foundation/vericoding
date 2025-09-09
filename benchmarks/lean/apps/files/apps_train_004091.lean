-- <vc-helpers>
-- </vc-helpers>

def sum_them (n : Nat) : Nat := sorry

@[simp]

theorem sum_them_non_negative (n : Nat) : 
  sum_them n ≥ 0 := sorry

@[simp] 

theorem sum_them_zero :
  sum_them 0 = 0 := sorry

theorem sum_them_monotonic (n : Nat) :
  n > 0 → sum_them n > sum_them (n-1) := sorry

theorem sum_them_closed_form (n : Nat) :
  n > 0 → sum_them n = 2^(n-1) * (2^n - 1) := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval sum_them 0

/-
info: 1
-/
-- #guard_msgs in
-- #eval sum_them 1

/-
info: 6
-/
-- #guard_msgs in
-- #eval sum_them 2

/-
info: 28
-/
-- #guard_msgs in
-- #eval sum_them 3

/-
info: 120
-/
-- #guard_msgs in
-- #eval sum_them 4

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible