-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def whoIsWinner (moves : List Move) (con sz : Nat) : Color :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem winner_result_valid (moves : List Move) (con sz : Nat) :
  whoIsWinner moves con sz = Color.Red ∨ 
  whoIsWinner moves con sz = Color.Yellow ∨
  whoIsWinner moves con sz = Color.Draw := 
  sorry

theorem empty_board_is_draw (con sz : Nat) : 
  con ≥ 2 → sz ≥ 2 →
  whoIsWinner [] con sz = Color.Draw := 
  sorry

theorem single_column_valid (moves : List Move) (col : Nat) (sz : Nat) :
  moves.length ≤ sz →
  (∀ m ∈ moves, m.col = col) →
  whoIsWinner moves 2 sz = Color.Red ∨
  whoIsWinner moves 2 sz = Color.Yellow ∨ 
  whoIsWinner moves 2 sz = Color.Draw := 
  sorry

theorem valid_board_yields_valid_result (moves : List Move) (con sz : Nat) :
  sz ≥ con →
  moves.length ≥ con →
  (∀ m ∈ moves, m.col < sz) →
  (∀ col, (moves.filter (λ m => m.col = col)).length ≤ sz) →
  whoIsWinner moves con sz = Color.Red ∨
  whoIsWinner moves con sz = Color.Yellow ∨
  whoIsWinner moves con sz = Color.Draw := 
  sorry

/-
info: 'R'
-/
-- #guard_msgs in
-- #eval whoIsWinner ["A_R", "B_Y", "A_R"] 2 2

/-
info: 'Y'
-/
-- #guard_msgs in
-- #eval whoIsWinner ["A_R", "C_Y", "C_R", "B_Y", "A_R", "C_Y", "B_R", "B_Y", "D_R", "A_Y", "D_R", "A_Y"] 2 4

/-
info: 'R'
-/
-- #guard_msgs in
-- #eval whoIsWinner ["E_R", "E_Y", "E_R", "A_Y", "B_R", "C_Y", "B_R", "F_Y", "F_R", "C_Y", "B_R", "D_Y", "D_R", "A_Y", "C_R", "E_Y", "B_R", "D_Y", "D_R", "A_Y", "A_R", "D_Y", "D_R"] 3 6
-- </vc-theorems>