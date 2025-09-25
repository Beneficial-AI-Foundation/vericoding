-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_valid_knight_move (move : String) : String := sorry

theorem valid_moves_only_returns_yes_or_no (pos1_col pos1_row pos2_col pos2_row : Char) 
    (h1 : 'a' ≤ pos1_col ∧ pos1_col ≤ 'h')
    (h2 : '1' ≤ pos1_row ∧ pos1_row ≤ '8')  
    (h3 : 'a' ≤ pos2_col ∧ pos2_col ≤ 'h')
    (h4 : '1' ≤ pos2_row ∧ pos2_row ≤ '8') :
    let move := s!"{pos1_col}{pos1_row}-{pos2_col}{pos2_row}"
    (is_valid_knight_move move = "Yes" ∨ is_valid_knight_move move = "No") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_format_returns_error (move : String) :
    (String.length move ≠ 5 ∨ 
     move.get ⟨2⟩ ≠ '-' ∨
     ¬('a' ≤ move.get ⟨0⟩ ∧ move.get ⟨0⟩ ≤ 'h') ∨
     ¬('1' ≤ move.get ⟨1⟩ ∧ move.get ⟨1⟩ ≤ '8') ∨
     ¬('a' ≤ move.get ⟨3⟩ ∧ move.get ⟨3⟩ ≤ 'h') ∨
     ¬('1' ≤ move.get ⟨4⟩ ∧ move.get ⟨4⟩ ≤ '8')) →
    is_valid_knight_move move = "Error" := sorry

theorem symmetric_moves (pos1_col pos1_row pos2_col pos2_row : Char)
    (h1 : 'a' ≤ pos1_col ∧ pos1_col ≤ 'h')
    (h2 : '1' ≤ pos1_row ∧ pos1_row ≤ '8')
    (h3 : 'a' ≤ pos2_col ∧ pos2_col ≤ 'h')
    (h4 : '1' ≤ pos2_row ∧ pos2_row ≤ '8') :
    let move1 := s!"{pos1_col}{pos1_row}-{pos2_col}{pos2_row}"
    let move2 := s!"{pos2_col}{pos2_row}-{pos1_col}{pos1_row}"
    is_valid_knight_move move1 = is_valid_knight_move move2 := sorry

theorem same_position_invalid (col row : Char)
    (h1 : 'a' ≤ col ∧ col ≤ 'h')
    (h2 : '1' ≤ row ∧ row ≤ '8') :
    let move := s!"{col}{row}-{col}{row}"
    is_valid_knight_move move = "No" := sorry
-- </vc-theorems>