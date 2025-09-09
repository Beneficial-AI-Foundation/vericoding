def min_moves_required (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def nat_sqrt (n : Nat) : Nat :=
  sorry

theorem min_moves_non_negative (n : Nat) (h : n > 0) : 
  min_moves_required n ≥ 0 := 
  sorry

theorem min_moves_less_than_input (n : Nat) (h : n > 0) :
  min_moves_required n ≤ n := 
  sorry

theorem min_moves_monotonic (n : Nat) (h : n > 1) :
  min_moves_required n ≥ min_moves_required (n-1) := 
  sorry 

theorem min_moves_base_case :
  min_moves_required 1 = 0 := 
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_moves_required 1

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_moves_required 5

/-
info: 11
-/
-- #guard_msgs in
-- #eval min_moves_required 42

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible