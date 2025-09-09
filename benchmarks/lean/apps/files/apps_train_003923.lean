-- <vc-helpers>
-- </vc-helpers>

def cake_slice (n : Nat) : Nat := sorry

theorem cake_slice_positive (n : Nat) :
  cake_slice n > 0 := sorry

theorem cake_slice_grows (n : Nat) :
  cake_slice n ≥ n + 1 := sorry 

theorem cake_slice_formula (n : Nat) :
  cake_slice n = (n * n + n + 2) / 2 := sorry

theorem cake_slice_bounded_growth (n : Nat) (h : n > 0) :
  cake_slice n ≤ cake_slice (n-1) + n := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval cake_slice 0

/-
info: 2
-/
-- #guard_msgs in
-- #eval cake_slice 1

/-
info: 4
-/
-- #guard_msgs in
-- #eval cake_slice 2

/-
info: 7
-/
-- #guard_msgs in
-- #eval cake_slice 3

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible