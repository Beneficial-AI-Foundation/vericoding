-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_weight_arrangements (n : Int) : Int := sorry

theorem small_known_values :
  (count_weight_arrangements 1 = 1) ∧ 
  (count_weight_arrangements 2 = 3) ∧
  (count_weight_arrangements 3 = 15) := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 3
-/
-- #guard_msgs in
-- #eval count_weight_arrangements 2

/-
info: 945
-/
-- #guard_msgs in
-- #eval count_weight_arrangements 5

/-
info: 221643095476699771875
-/
-- #guard_msgs in
-- #eval count_weight_arrangements 18
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible