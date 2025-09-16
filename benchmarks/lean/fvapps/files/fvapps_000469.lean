-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def least_bricks (wall : List (List Nat)) : Nat := sorry

theorem least_bricks_identical_rows (n : Nat)
  (h : n > 0) :
  least_bricks (List.replicate n [1, 1]) = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem least_bricks_empty :
  least_bricks [] = 0 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval least_bricks [[1, 2, 2, 1], [3, 1, 2], [1, 3, 2], [2, 4], [3, 1, 2], [1, 3, 1, 1]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval least_bricks []

/-
info: 3
-/
-- #guard_msgs in
-- #eval least_bricks [[5], [5], [5]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible