-- <vc-helpers>
-- </vc-helpers>

def duty_free (price : Int) (discount : Int) (holiday_cost : Int) : Int :=
sorry

theorem duty_free_result_nonnegative
  (price : Int) (discount : Int) (holiday_cost : Int)
  (h1 : price > 0) (h2 : discount > 0) (h3 : holiday_cost > 0)
  (h4 : discount < 100) :
  duty_free price discount holiday_cost ≥ 0 :=
sorry

theorem duty_free_calculation_matches_formula
  (price : Int) (discount : Int) (holiday_cost : Int)
  (h1 : price > 0) (h2 : discount > 0) (h3 : holiday_cost > 0)
  (h4 : discount < 100) :
  duty_free price discount holiday_cost = 
    Int.toNat (holiday_cost * 100 / (price * discount)) :=
sorry

theorem duty_free_total_savings_exceeds_holiday_cost
  (price : Int) (discount : Int) (holiday_cost : Int)
  (h1 : price > 0) (h2 : discount > 0) (h3 : holiday_cost > 0)
  (h4 : discount < 100) :
  (price * discount * (duty_free price discount holiday_cost + 1)) / 100 > holiday_cost :=
sorry

theorem duty_free_100_percent_discount
  (price : Int) (holiday_cost : Int)
  (h1 : price > 0) (h2 : holiday_cost > 0) :
  duty_free price 100 holiday_cost = holiday_cost / price :=
sorry

theorem duty_free_zero_inputs_error1
  (discount : Int) (holiday_cost : Int) :
  duty_free 0 discount holiday_cost = 0 :=
sorry 

theorem duty_free_zero_inputs_error2
  (price : Int) (holiday_cost : Int) :
  duty_free price 0 holiday_cost = 0 :=
sorry

/-
info: 166
-/
-- #guard_msgs in
-- #eval duty_free 12 50 1000

/-
info: 294
-/
-- #guard_msgs in
-- #eval duty_free 17 10 500

/-
info: 357
-/
-- #guard_msgs in
-- #eval duty_free 24 35 3000

-- Apps difficulty: introductory
-- Assurance level: unguarded