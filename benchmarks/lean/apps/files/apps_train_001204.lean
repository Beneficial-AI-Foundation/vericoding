-- <vc-helpers>
-- </vc-helpers>

def solve_min_swaps (n : Nat) (k : Nat) (arr : List Nat) : Int := sorry

theorem solve_min_swaps_known_cases_1 :
  solve_min_swaps 5 2 [3, 4, 5, 2, 1] = 3 := sorry

theorem solve_min_swaps_known_cases_2 :
  solve_min_swaps 5 2 [4, 3, 2, 1, 5] = -1 := sorry

theorem solve_min_swaps_known_cases_3 :
  solve_min_swaps 3 3 [3, 2, 1] = -1 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_min_swaps 5 2 [3, 4, 5, 2, 1]

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve_min_swaps 5 2 [4, 3, 2, 1, 5]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible