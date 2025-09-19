-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rental_car_cost (days : Int) : Int := sorry

theorem rental_cost_always_positive {days : Int} (h : days > 0) : 
  rental_car_cost days ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rental_base_calculation (days : Int) :
  (days < 3 → rental_car_cost days = days * 40) ∧
  (3 ≤ days ∧ days < 7 → rental_car_cost days = days * 40 - 20) ∧
  (days ≥ 7 → rental_car_cost days = days * 40 - 50) := sorry

theorem no_discount_short_rental {days : Int} (h1 : days ≤ 2) (h2 : days > 0) :
  rental_car_cost days = days * 40 := sorry

theorem long_rental_discount {days : Int} (h : days ≥ 7) :
  rental_car_cost days = days * 40 - 50 := sorry

theorem medium_rental_discount {days : Int} (h1 : days ≥ 3) (h2 : days ≤ 6) :
  rental_car_cost days = days * 40 - 20 := sorry
-- </vc-theorems>