-- <vc-helpers>
-- </vc-helpers>

def solve_marbles_game (n: Int) : String := sorry

theorem solve_marbles_game_returns_valid_player (n: Int) :
  solve_marbles_game n = "A" ∨ solve_marbles_game n = "B" := sorry

theorem large_n_returns_b (n: Int) (h: n ≥ 4) :
  solve_marbles_game n = "B" := sorry

theorem small_n_returns_b (n: Int) (h: n ≤ 2) :
  solve_marbles_game n = "B" := sorry

theorem three_marbles_returns_a :
  solve_marbles_game 3 = "A" := sorry

/-
info: 'B'
-/
-- #guard_msgs in
-- #eval solve_marbles_game 1

/-
info: 'A'
-/
-- #guard_msgs in
-- #eval solve_marbles_game 3

/-
info: 'B'
-/
-- #guard_msgs in
-- #eval solve_marbles_game 7

-- Apps difficulty: interview
-- Assurance level: unguarded