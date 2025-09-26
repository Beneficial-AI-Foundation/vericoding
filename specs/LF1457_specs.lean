-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def determine_winner (rows cols : Nat) : Player := sorry

theorem determine_winner_returns_valid_player (rows cols : Nat) 
  (h1 : 1 ≤ rows) (h2 : rows ≤ 1000) (h3 : 1 ≤ cols) (h4 : cols ≤ 1000) :
  (determine_winner rows cols = Player.Vanya) ∨ 
  (determine_winner rows cols = Player.Tuzik) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem winner_pattern_properties (rows cols : Nat)
  (h1 : 1 ≤ rows) (h2 : rows ≤ 1000) (h3 : 1 ≤ cols) (h4 : cols ≤ 1000) :
  let row_mod := (rows - 1) % 4
  let col_mod := (cols - 1) % 3
  ((col_mod = 0 ∧ row_mod = 0) ∨ 
   (col_mod = 1 ∧ row_mod = 1) ∨ 
   (col_mod = 2 ∧ row_mod = 2)) → determine_winner rows cols = Player.Vanya 
  ∧
  ¬((col_mod = 0 ∧ row_mod = 0) ∨ 
    (col_mod = 1 ∧ row_mod = 1) ∨ 
    (col_mod = 2 ∧ row_mod = 2)) → determine_winner rows cols = Player.Tuzik := sorry

theorem column_periodicity (rows : Nat) (h1 : 1 ≤ rows) (h2 : rows ≤ 1000) :
  ∀ col : Nat, 1 ≤ col → col ≤ 3 →
    determine_winner rows col = determine_winner rows (col + 3) := sorry

theorem row_periodicity (cols : Nat) (h1 : 1 ≤ cols) (h2 : cols ≤ 1000) :
  ∀ row : Nat, 1 ≤ row → row ≤ 4 →
    determine_winner row cols = determine_winner (row + 4) cols := sorry

/-
info: 'Tuzik'
-/
-- #guard_msgs in
-- #eval determine_winner 4 4

/-
info: 'Vanya'
-/
-- #guard_msgs in
-- #eval determine_winner 2 2

/-
info: 'Vanya'
-/
-- #guard_msgs in
-- #eval determine_winner 5 4
-- </vc-theorems>