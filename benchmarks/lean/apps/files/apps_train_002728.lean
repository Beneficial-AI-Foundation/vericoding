-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mobius (n : Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mobius_output_range (n : Nat) (h : n > 0) : 
  mobius n = -1 ∨ mobius n = 0 ∨ mobius n = 1 :=
  sorry

theorem mobius_square_factors (n : Nat) (h : n > 1) :
  mobius (n * n) = 0 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval mobius 10

/-
info: 0
-/
-- #guard_msgs in
-- #eval mobius 9

/-
info: -1
-/
-- #guard_msgs in
-- #eval mobius 7
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible