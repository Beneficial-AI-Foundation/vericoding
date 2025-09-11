-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_balloon_game (r g b k : Nat) : Nat := sorry

theorem balloon_game_result_lower_bound
  (r g b k : Nat) (h : k > 0) :
  solve_balloon_game r g b k ≥ 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem balloon_game_result_upper_bound
  (r g b k : Nat) (h : k > 0) :
  solve_balloon_game r g b k ≤ 1 + min r (k-1) + min g (k-1) + min b (k-1) := sorry

theorem balloon_game_k_one
  (r g b : Nat) :
  solve_balloon_game r g b 1 = 1 := sorry

theorem balloon_game_single_color
  (count k : Nat) (h : k > 1) :
  solve_balloon_game count 0 0 k = min count (k-1) + 1 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_balloon_game 3 3 3 1

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_balloon_game 3 3 3 2

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve_balloon_game 10 5 2 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible