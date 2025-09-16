-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nth_person_gets_nth_seat (n : Nat) : Float := sorry

theorem prob_bounds (n : Nat) (h : n > 0) : 
  0 ≤ nth_person_gets_nth_seat n ∧ nth_person_gets_nth_seat n ≤ 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_first_person_prob (n : Nat) (h : n > 1) :
  nth_person_gets_nth_seat n = 0.5 := sorry

theorem first_person_prob :
  nth_person_gets_nth_seat 1 = 1.0 := sorry

/-
info: 1.0
-/
-- #guard_msgs in
-- #eval nth_person_gets_nth_seat 1

/-
info: 0.5
-/
-- #guard_msgs in
-- #eval nth_person_gets_nth_seat 2

/-
info: 0.5
-/
-- #guard_msgs in
-- #eval nth_person_gets_nth_seat 100
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded