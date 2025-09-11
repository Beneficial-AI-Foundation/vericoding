-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mct_from_leaf_values (arr : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem base_cases :
  mct_from_leaf_values [] = 0 ∧
  mct_from_leaf_values [5] = 0 ∧ 
  mct_from_leaf_values [4, 11] = 44 :=
  sorry

/-
info: 32
-/
-- #guard_msgs in
-- #eval mct_from_leaf_values [6, 2, 4]

/-
info: 44
-/
-- #guard_msgs in
-- #eval mct_from_leaf_values [4, 11]

/-
info: 500
-/
-- #guard_msgs in
-- #eval mct_from_leaf_values [15, 13, 5, 3, 15]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible