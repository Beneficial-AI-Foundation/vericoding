-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_step (board: String) (hand: String) : Int := sorry

theorem find_min_step_returns_valid_result 
  (board: String) (hand: String) : 
  find_min_step board hand ≥ -1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_step_empty_board
  (hand: String) :
  find_min_step "" hand = 0 := sorry 

theorem find_min_step_empty_hand_nonempty_board
  (board: String) (h1: board.length > 0) :
  find_min_step board "" = -1 := sorry

theorem find_min_step_empty_empty : 
  find_min_step "" "" = 0 := sorry
-- </vc-theorems>