-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def make_valid_board (pawn_positions : List Nat) (length : Nat) : String := sorry
def can_ada_win (board : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_valid (board : String) : 
  can_ada_win board = "Yes" ∨ can_ada_win board = "No" := sorry

theorem adjacent_pawns_lose (n : Nat) : 
  n ≥ 2 → can_ada_win (String.mk (List.replicate (n-2) '.' ++ ['P', 'P'])) = "No" := sorry

theorem empty_board_loses_3 :
  can_ada_win "..." = "No" := sorry

theorem empty_board_loses_1 :
  can_ada_win "." = "No" := sorry

theorem empty_board_loses (n : Nat) (h : n > 0) :
  can_ada_win (String.mk (List.replicate n '.')) = "No" := sorry
-- </vc-theorems>