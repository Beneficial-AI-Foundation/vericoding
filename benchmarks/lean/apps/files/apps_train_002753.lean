-- <vc-helpers>
-- </vc-helpers>

def plant_doubling (n : Nat) : Nat := sorry

theorem plant_doubling_output_range (n : Nat) (h : n > 0) :
  1 ≤ plant_doubling n ∧ plant_doubling n ≤ n := sorry

theorem plant_doubling_edge_cases :
  plant_doubling 1 = 1 ∧
  plant_doubling 2 = 1 ∧  
  plant_doubling 3 = 2 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval plant_doubling 5

/-
info: 1
-/
-- #guard_msgs in
-- #eval plant_doubling 8

/-
info: 1
-/
-- #guard_msgs in
-- #eval plant_doubling 1

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible