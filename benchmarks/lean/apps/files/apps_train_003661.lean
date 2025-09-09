-- <vc-helpers>
-- </vc-helpers>

def solve (a b : Nat) : Nat := sorry 

theorem solve_range_bounds (a b : Nat) (h1 : a ≤ 499999) (h2 : b ≤ 499999) : 
  solve (min a b) (max a b) ≥ 0 := sorry

theorem solve_same_bounds (x : Nat) (h : x ≤ 499999) : 
  solve x x ≥ 0 := sorry

theorem solve_zero :
  solve 0 0 = 0 := sorry

theorem solve_monotonic (x : Nat) (h : x ≤ 499999) : 
  solve 0 x ≤ solve 0 (x + 1) := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve 0 10

/-
info: 1080
-/
-- #guard_msgs in
-- #eval solve 2 200

/-
info: 48132
-/
-- #guard_msgs in
-- #eval solve 200 2000

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible