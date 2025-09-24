-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def angle_between_hands (hour : Nat) (minutes : Nat) : Float := sorry 

theorem angle_between_hands_returns_valid_angle 
  (hour : Nat) (minutes : Nat)
  (h1 : 1 ≤ hour ∧ hour ≤ 12) 
  (h2 : minutes ≤ 59) :
  0 ≤ angle_between_hands hour minutes ∧ 
  angle_between_hands hour minutes ≤ 180 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem angle_calculation_periodic
  (hour : Nat) (minutes : Nat)
  (h1 : 1 ≤ hour ∧ hour ≤ 12)
  (h2 : minutes ≤ 59) :
  (angle_between_hands hour minutes - 
   angle_between_hands (if hour ≠ 12 then hour else 12) minutes) < 0.00001 := sorry

theorem angle_is_minimal
  (hour : Nat) (minutes : Nat) 
  (h1 : 1 ≤ hour ∧ hour ≤ 12)
  (h2 : minutes ≤ 59) :
  angle_between_hands hour minutes ≤ 180 := sorry
-- </vc-theorems>