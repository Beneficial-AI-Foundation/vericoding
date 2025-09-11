-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def playerRankUp (points : Int) : Bool ⊕ String := sorry 

theorem playerRankUp_return_type (points : Int) : 
  (∃ b : Bool, playerRankUp points = Sum.inl b) ∨ 
  (∃ s : String, playerRankUp points = Sum.inr s) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem below_threshold (points : Int) :
  points < 100 → playerRankUp points = Sum.inl false := sorry 

theorem above_threshold (points : Int) :
  points ≥ 100 → 
  playerRankUp points = Sum.inr "Well done! You have advanced to the qualifying stage. Win 2 out of your next 3 games to rank up." := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval playerRankUp 45

/-
info: 'Well done! You have advanced to the qualifying stage. Win 2 out of your next 3 games to rank up.'
-/
-- #guard_msgs in
-- #eval playerRankUp 100

/-
info: 'Well done! You have advanced to the qualifying stage. Win 2 out of your next 3 games to rank up.'
-/
-- #guard_msgs in
-- #eval playerRankUp 105
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded