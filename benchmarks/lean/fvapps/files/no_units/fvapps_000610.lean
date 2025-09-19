-- <vc-preamble>
def gameWinner (config : String) : String := sorry

theorem gameWinner_returns_valid_player (config : String) :
  (gameWinner config = "Chef" ∨ gameWinner config = "Aleksa") := 
sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countBlacksBeforeWhite (s : String) : Nat := sorry
def countBlacksAfterWhite (s : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem chef_wins_equal_blacks (config : String)
  (h : countBlacksBeforeWhite config = countBlacksAfterWhite config) :
  gameWinner config = "Chef" := 
sorry

theorem aleksa_wins_unequal_blacks (config : String)
  (h : countBlacksBeforeWhite config ≠ countBlacksAfterWhite config) :
  gameWinner config = "Aleksa" :=
sorry

theorem chef_wins_single_white (config : String)
  (h : config = "W") :
  gameWinner config = "Chef" :=
sorry
-- </vc-theorems>