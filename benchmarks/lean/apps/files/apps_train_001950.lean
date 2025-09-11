-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_tournament_max_games (n: Nat) (k: Nat) (teams: List Nat) : Nat := sorry

theorem tournament_result_non_negative (n k: Nat) (teams: List Nat) :
  solve_tournament_max_games n k teams ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tournament_result_bounded (n k: Nat) (teams: List Nat) :
  solve_tournament_max_games n k teams ≤ (2^n - 1 + 2^n + 1) := sorry

theorem empty_tournament_zero_games (n: Nat) :
  solve_tournament_max_games n 0 [] = 0 := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve_tournament_max_games 3 1 [6]

/-
info: 11
-/
-- #guard_msgs in
-- #eval solve_tournament_max_games 3 3 [1, 7, 8]

/-
info: 14
-/
-- #guard_msgs in
-- #eval solve_tournament_max_games 3 4 [1, 3, 5, 7]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded