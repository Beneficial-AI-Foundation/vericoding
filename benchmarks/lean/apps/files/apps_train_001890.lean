-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def num_tilings (n : Int) : Int := sorry

theorem num_tilings_base_cases : 
  num_tilings 1 = 1 ∧ num_tilings 2 = 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem num_tilings_small_sequence :
  num_tilings 1 = 1 ∧
  num_tilings 2 = 2 ∧
  num_tilings 3 = 5 ∧
  num_tilings 4 = 11 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval num_tilings 3

/-
info: 1
-/
-- #guard_msgs in
-- #eval num_tilings 1

/-
info: 11
-/
-- #guard_msgs in
-- #eval num_tilings 4
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible