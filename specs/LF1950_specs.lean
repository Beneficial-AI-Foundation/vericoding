-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>