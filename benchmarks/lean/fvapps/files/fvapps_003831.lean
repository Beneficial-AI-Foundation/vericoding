-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chess_knight (pos : String) : Nat := sorry

theorem corner_positions (pos : String) :
  (pos = "a1" ∨ pos = "a8" ∨ pos = "h1" ∨ pos = "h8") → chess_knight pos = 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem edge_positions (pos : String) :
  ((pos.front = 'a' ∨ pos.front = 'h' ∨ 
    pos.back = '1' ∨ pos.back = '8') ∧
   ¬(pos = "a1" ∨ pos = "a8" ∨ pos = "h1" ∨ pos = "h8")) →
  chess_knight pos ≤ 4 := sorry

theorem center_max_moves :
  chess_knight "d4" = 8 ∧ chess_knight "e4" = 8 := sorry
-- </vc-theorems>