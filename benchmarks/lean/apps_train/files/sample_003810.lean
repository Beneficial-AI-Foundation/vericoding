/-
Mike and Joe are fratboys that love beer and games that involve drinking. They play the following game: Mike chugs one beer, then Joe chugs 2 beers, then Mike chugs 3 beers, then Joe chugs 4 beers, and so on. Once someone can't drink what he is supposed to drink, he loses.

Mike can chug at most A beers in total (otherwise he would pass out), while Joe can chug at most B beers in total. Who will win the game? 

Write the function ```game(A,B)``` that returns the winner, ```"Mike"``` or ```"Joe"``` accordingly, for any given integer values of A and B.

Note: If either Mike or Joe cannot drink at least 1 beer, return the string  ```"Non-drinkers can't play"```.
-/

-- <vc-helpers>
-- </vc-helpers>

def game (mike : Nat) (joe : Nat) : GameResult :=
  sorry

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

-- Apps difficulty: introductory
-- Assurance level: unguarded