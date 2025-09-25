-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isWhite (p: Piece) : Bool := sorry 

def fight_resolve (defender attacker : Piece) : Option Piece := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem same_team_invalid {d a : Piece} : 
  isWhite d = isWhite a → fight_resolve d a = none := sorry

theorem result_is_valid {d a : Piece} :
  fight_resolve d a = some d ∨ fight_resolve d a = some a ∨ fight_resolve d a = none := sorry

theorem winning_matchups_symmetrical {d a : Piece} :
  fight_resolve d a = some d →
  ((d = Piece.King ∧ a = Piece.Assassin) ∨
   (d = Piece.Shield ∧ a = Piece.Pike) ∨ 
   (d = Piece.Assassin ∧ a = Piece.Shield) ∨
   (d = Piece.Pike ∧ a = Piece.King)) := sorry

theorem default_attacker_wins {d a : Piece} :
  fight_resolve d a ≠ none →
  fight_resolve d a ≠ some d →
  fight_resolve d a = some a := sorry

/-
info: -1
-/
-- #guard_msgs in
-- #eval fight_resolve "K" "A"

/-
info: 'k'
-/
-- #guard_msgs in
-- #eval fight_resolve "k" "A"

/-
info: 'P'
-/
-- #guard_msgs in
-- #eval fight_resolve "a" "P"
-- </vc-theorems>