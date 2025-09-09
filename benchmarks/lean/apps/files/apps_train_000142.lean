-- <vc-helpers>
-- </vc-helpers>

def min_steps (n : Nat) : Nat := sorry

def isPrime (n : Nat) : Bool := sorry

theorem min_steps_nonnegative (n : Nat) (h : n ≥ 1) : 
  min_steps n ≥ 0 := sorry

theorem min_steps_upper_bound (n : Nat) (h : n ≥ 2) :
  min_steps n ≤ n := sorry 

theorem min_steps_small_numbers :
  min_steps 1 = 0 ∧ 
  min_steps 2 = 2 ∧
  min_steps 4 = 4 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_steps 3

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_steps 1

/-
info: 6
-/
-- #guard_msgs in
-- #eval min_steps 9

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible