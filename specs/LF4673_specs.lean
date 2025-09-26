-- <vc-preamble>
def Pong.play (game : Pong) (ballPos playerPos : Int) : String := sorry

def Pong.game_over (game : Pong) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Int.abs (i : Int) : Int := sorry

theorem pong_init_properties {maxScore : Nat} (h : maxScore ≥ 1) :
  let game := Pong.mk maxScore []
  game.maxScore = maxScore ∧ 
  game.scores = [] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hit_or_miss_range {maxScore : Nat} {ballPos playerPos : Int} 
  (h1 : maxScore ≥ 2) :
  let game := Pong.mk maxScore []
  let result := game.play ballPos playerPos
  (Int.abs (ballPos - playerPos) ≤ 3 → result.contains '.') ∧
  (Int.abs (ballPos - playerPos) > 3 ∧ ¬result.contains '.' → result.contains ' ') := sorry

theorem alternating_players {maxScore : Nat} (h : maxScore ≥ 1) :
  let game := Pong.mk maxScore []
  let plays := [game.play 10 0, game.play 10 0, game.play 10 0, game.play 10 0]
  ∀ i, i + 1 < plays.length → 
    let p1 := plays[i]!
    let p2 := plays[i+1]!
    p1 ≠ p2 := sorry

theorem game_over_condition {maxScore : Nat} (h : maxScore ≥ 1) :
  let game := Pong.mk maxScore []
  ∃ plays : List String, 
    let last := plays.getLast! 
    last.contains ' ' ∧
    game.play 0 0 = "Game Over!" := sorry
-- </vc-theorems>