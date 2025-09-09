-- <vc-helpers>
-- </vc-helpers>

def number_ways (hats : List (List Nat)) : Nat :=
  sorry

theorem number_ways_basic_cases1 :
  number_ways [[3,4], [4,5], [5]] = 1 :=
sorry

theorem number_ways_basic_cases2 :
  number_ways [[3,5,1], [3,5]] = 4 :=
sorry

theorem number_ways_empty :
  number_ways [] = 1 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval number_ways [[3, 4], [4, 5], [5]]

/-
info: 4
-/
-- #guard_msgs in
-- #eval number_ways [[3, 5, 1], [3, 5]]

/-
info: 24
-/
-- #guard_msgs in
-- #eval number_ways [[1, 2, 3, 4], [1, 2, 3, 4], [1, 2, 3, 4], [1, 2, 3, 4]]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible