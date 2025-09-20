-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_restaurant_area (points : List (Int × Int)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>