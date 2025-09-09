-- <vc-helpers>
-- </vc-helpers>

def count_heavy_bags (size : Nat) (weights : List Nat) : Nat := sorry

theorem count_heavy_bags_bounds (size : Nat) (weights : List Nat) :
  let result := count_heavy_bags size weights
  0 ≤ result ∧ result ≤ weights.length := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_heavy_bags 4 [1, 2, 3, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_heavy_bags 3 [1, 1, 1]

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_heavy_bags 5 [5, 4, 3, 2, 1]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible