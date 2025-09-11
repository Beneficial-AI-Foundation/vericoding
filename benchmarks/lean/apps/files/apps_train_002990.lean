-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def number_of_pairs (gloves : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pairs_non_negative (gloves : List String) :
  number_of_pairs gloves ≥ 0 :=
sorry

theorem pairs_at_most_half (gloves : List String) :
  number_of_pairs gloves ≤ gloves.length / 2 :=
sorry

theorem empty_list_zero : 
  number_of_pairs [] = 0 :=
sorry

theorem duplicate_list_pairs (gloves : List String) :
  number_of_pairs (gloves ++ gloves) = gloves.length :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval number_of_pairs ["red", "red"]

/-
info: 0
-/
-- #guard_msgs in
-- #eval number_of_pairs ["red", "green", "blue"]

/-
info: 3
-/
-- #guard_msgs in
-- #eval number_of_pairs ["gray", "black", "purple", "purple", "gray", "black"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible