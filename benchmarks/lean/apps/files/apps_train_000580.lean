-- <vc-helpers>
-- </vc-helpers>

def calculate_restaurant_area (points : List (Int × Int)) : Int :=
  sorry

theorem restaurant_area_nonnegative {points : List (Int × Int)} :
  calculate_restaurant_area points ≥ 0 :=
sorry

theorem restaurant_area_linear_scaling {points : List (Int × Int)} :
  calculate_restaurant_area ((points.map (fun p => (p.1, 2 * p.2)))) = 
  2 * calculate_restaurant_area points :=
sorry 

theorem restaurant_area_shift_invariant {points : List (Int × Int)} :
  calculate_restaurant_area ((points.map (fun p => (p.1 + 10, p.2)))) = 
  calculate_restaurant_area points :=
sorry

theorem restaurant_area_zero_height {points : List (Int × Int)} :
  calculate_restaurant_area ((points.map (fun p => (p.1, 0)))) = 0 :=
sorry

/-
info: 27
-/
-- #guard_msgs in
-- #eval calculate_restaurant_area [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5)]

-- Apps difficulty: interview
-- Assurance level: guarded