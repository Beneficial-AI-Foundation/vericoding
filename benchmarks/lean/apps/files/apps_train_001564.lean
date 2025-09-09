def BowlingFrame := String
def BowlingGame := String

-- <vc-helpers>
-- </vc-helpers>

def bowling_score (game : BowlingGame) : Nat :=
  sorry

theorem score_zero_game :
  bowling_score "00 00 00 00 00 00 00 00 00 00" = 0 :=
  sorry

theorem score_perfect_game :
  bowling_score "X X X X X X X X X XXX" = 300 :=
  sorry

theorem score_all_ones :
  bowling_score "11 11 11 11 11 11 11 11 11 11" = 20 :=
  sorry

theorem score_mixed_game :
  bowling_score "X X 9/ 80 X X 90 8/ 7/ 44" = 171 :=
  sorry

theorem score_all_spares :
  bowling_score "5/ 5/ 5/ 5/ 5/ 5/ 5/ 5/ 5/ 5/5" = 150 :=
  sorry

/-
info: 20
-/
-- #guard_msgs in
-- #eval bowling_score "11 11 11 11 11 11 11 11 11 11"

/-
info: 300
-/
-- #guard_msgs in
-- #eval bowling_score "X X X X X X X X X XXX"

/-
info: 171
-/
-- #guard_msgs in
-- #eval bowling_score "X X 9/ 80 X X 90 8/ 7/ 44"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible