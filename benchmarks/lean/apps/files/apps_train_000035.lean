-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_explorer_groups (N : Nat) (explorers : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_explorer_groups_all_ones
    (n : Nat) (h : n > 0 ∧ n ≤ 5)
    (explorers : List Nat) (h' : explorers = List.replicate n 1) :
    solve_explorer_groups n explorers = n :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_explorer_groups 3 [1, 1, 1]

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_explorer_groups 5 [2, 3, 1, 2, 2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_explorer_groups 4 [1, 2, 3, 4]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible