-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rps (p1 p2 : Move) : Outcome :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rps_symmetry (p1 p2 : Move) :
  match rps p1 p2 with
  | Outcome.draw => rps p2 p1 = Outcome.draw
  | Outcome.player1Wins => rps p2 p1 = Outcome.player2Wins
  | Outcome.player2Wins => rps p2 p1 = Outcome.player1Wins
  := sorry

theorem rps_draw (m : Move) :
  rps m m = Outcome.draw := sorry

theorem rps_valid_result (p1 p2 : Move) :
  match rps p1 p2 with
  | Outcome.player1Wins => True
  | Outcome.player2Wins => True
  | Outcome.draw => True := sorry

/-
info: 'Player 1 won!'
-/
-- #guard_msgs in
-- #eval rps "rock" "scissors"

/-
info: 'Player 2 won!'
-/
-- #guard_msgs in
-- #eval rps "scissors" "rock"

/-
info: 'Draw!'
-/
-- #guard_msgs in
-- #eval rps "rock" "rock"
-- </vc-theorems>