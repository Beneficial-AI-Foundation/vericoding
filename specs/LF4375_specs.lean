-- <vc-preamble>
def opposite : Player → Player 
  | Player.black => Player.white
  | Player.white => Player.black
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def whoseMove (player : Player) (win : Bool) : Player := sorry

theorem whoseMove_valid (player : Player) (win : Bool) :
  whoseMove player win = player ∨ whoseMove player win = opposite player := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem whoseMove_win (player : Player) (win : Bool) :
  win = true → whoseMove player win = player := by sorry

theorem whoseMove_lose (player : Player) (win : Bool) :
  win = false → whoseMove player win = opposite player := by sorry

/-
info: 'white'
-/
-- #guard_msgs in
-- #eval whoseMove "black" False

/-
info: 'white'
-/
-- #guard_msgs in
-- #eval whoseMove "white" True

/-
info: 'black'
-/
-- #guard_msgs in
-- #eval whoseMove "black" True
-- </vc-theorems>