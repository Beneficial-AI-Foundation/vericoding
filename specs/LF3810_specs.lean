-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def game (mike : Nat) (joe : Nat) : GameResult :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem game_returns_valid_result (mike joe : Nat) :
  let result := game mike joe
  result = GameResult.Mike ∨ result = GameResult.Joe ∨ result = GameResult.NonDrinkers
  := sorry

theorem game_deterministic (mike joe : Nat) :
  game mike joe = game mike joe := sorry

theorem game_non_drinkers :
  (game 0 1 = GameResult.NonDrinkers) ∧
  (game 1 0 = GameResult.NonDrinkers) ∧
  (game 0 0 = GameResult.NonDrinkers) := sorry

theorem game_positive_inputs_valid_winner (mike joe : Nat) :
  mike > 0 → joe > 0 →
  let result := game mike joe
  result = GameResult.Mike ∨ result = GameResult.Joe := sorry

/-
info: 'Joe'
-/
-- #guard_msgs in
-- #eval game 3 2

/-
info: 'Mike'
-/
-- #guard_msgs in
-- #eval game 4 2

/-
info: "Non-drinkers can't play"
-/
-- #guard_msgs in
-- #eval game 0 1
-- </vc-theorems>