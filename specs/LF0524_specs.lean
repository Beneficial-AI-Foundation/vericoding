-- <vc-preamble>
def determine_winner (S : Nat) (SG : Nat) (FG : Nat) (D : Nat) (T : Nat) : Winner :=
  sorry

def abs (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nat_minus (a b : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem determine_winner_valid (S SG FG D T : Nat) :
  ∃ w : Winner, determine_winner S SG FG D T = w
  := sorry

theorem determine_winner_draw_when_equidistant (S SG FG D T : Nat) :
  let actual_speed := (D * 50 * 3600)/(T * 1000) + S
  nat_minus (abs (nat_minus SG actual_speed)) (abs (nat_minus FG actual_speed)) = 0 →
  determine_winner S SG FG D T = Winner.DRAW
  := sorry

theorem determine_winner_father_when_further (S SG FG D T : Nat) :
  let actual_speed := (D * 50 * 3600)/(T * 1000) + S
  nat_minus (abs (nat_minus SG actual_speed)) (abs (nat_minus FG actual_speed)) > 0 →
  determine_winner S SG FG D T = Winner.FATHER
  := sorry

theorem determine_winner_sebi_when_closer (S SG FG D T : Nat) :
  let actual_speed := (D * 50 * 3600)/(T * 1000) + S
  nat_minus (abs (nat_minus SG actual_speed)) (abs (nat_minus FG actual_speed)) < 0 →
  determine_winner S SG FG D T = Winner.SEBI
  := sorry

theorem determine_winner_same_guess_draw (S G D T : Nat) :
  determine_winner S G G D T = Winner.DRAW
  := sorry

/-
info: 'SEBI'
-/
-- #guard_msgs in
-- #eval determine_winner 100 180 200 20 60

/-
info: 'FATHER'
-/
-- #guard_msgs in
-- #eval determine_winner 130 131 132 1 72

/-
info: 'DRAW'
-/
-- #guard_msgs in
-- #eval determine_winner 100 150 150 10 30
-- </vc-theorems>