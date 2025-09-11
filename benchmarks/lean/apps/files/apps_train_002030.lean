-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_visible_kangaroos (n : Nat) (sizes : List Nat) : Nat := sorry

theorem min_visible_kangaroos_edge_cases :
  min_visible_kangaroos 1 [1] = 1 ∧
  min_visible_kangaroos 2 [1, 3] = 1 ∧
  min_visible_kangaroos 3 [1, 2, 4] = 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 5
-/
-- #guard_msgs in
-- #eval min_visible_kangaroos 8 [2, 5, 7, 6, 9, 8, 4, 2]

/-
info: 5
-/
-- #guard_msgs in
-- #eval min_visible_kangaroos 8 [9, 1, 6, 2, 6, 5, 8, 3]

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_visible_kangaroos 5 [1, 2, 4, 8, 16]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible