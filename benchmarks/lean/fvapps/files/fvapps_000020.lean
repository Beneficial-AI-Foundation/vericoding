-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CustomerInfo := List (Nat × Int × Int)

def check_restaurant_temps (initial_temp : Int) (customer_info : CustomerInfo) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_restaurant_temps_returns_valid_string (initial_temp : Int) (customer_info : CustomerInfo) :
  check_restaurant_temps initial_temp customer_info = "YES" ∨ 
  check_restaurant_temps initial_temp customer_info = "NO" :=
  sorry

theorem customer_info_time_monotonic {info : CustomerInfo} :
  ∀ i j, i < j → j < info.length → 
    (info.get! i).1 ≤ (info.get! j).1 :=
  sorry

theorem empty_customer_info_returns_yes (initial_temp : Int) :
  check_restaurant_temps initial_temp [] = "YES" :=
  sorry

theorem single_customer_response (initial_temp : Int) (t : Nat) (l h : Int) :
  let temp_range_low := initial_temp - t
  let temp_range_high := initial_temp + t
  let customer_info := [(t, l, h)]
  (h < temp_range_low ∨ temp_range_high < l → 
    check_restaurant_temps initial_temp customer_info = "NO") ∧
  (¬(h < temp_range_low ∨ temp_range_high < l) → 
    check_restaurant_temps initial_temp customer_info = "YES") :=
  sorry
-- </vc-theorems>