-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def convert_bits (a b : Int) : Int := sorry

theorem convert_from_zero_cases :
  (convert_bits 0 0 = 0) ∧ 
  (convert_bits 0 1 = 1) ∧
  (convert_bits 0 2 = 1) ∧ 
  (convert_bits 0 3 = 2) ∧
  (convert_bits 0 4 = 1) := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 2
-/
-- #guard_msgs in
-- #eval convert_bits 31 14

/-
info: 3
-/
-- #guard_msgs in
-- #eval convert_bits 7 17

/-
info: 0
-/
-- #guard_msgs in
-- #eval convert_bits 0 0
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible