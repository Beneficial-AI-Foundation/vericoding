-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_peace_distance (houses : List Int) : Int := sorry

theorem peace_distance_nonnegative (houses : List Int) 
  (h : houses.length ≥ 2) :
  find_max_peace_distance houses ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem peace_distance_upper_bound (houses : List Int)
  (h : houses.length ≥ 2) :
  find_max_peace_distance houses ≤ (List.maximum? houses).getD 0 - (List.minimum? houses).getD 0 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_max_peace_distance [7, -1, 2, 13, -5, 15]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_peace_distance [6, 10, 3, 12]

/-
info: 10
-/
-- #guard_msgs in
-- #eval find_max_peace_distance [-5, 0, 10]
-- </vc-theorems>