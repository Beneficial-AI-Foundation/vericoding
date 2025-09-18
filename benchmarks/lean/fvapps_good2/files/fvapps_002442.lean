-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_shoe_shop_earnings (num_shoes : Nat) (shoe_sizes : List Nat)
    (customer_requests : List (Nat × Nat)) : Nat :=
  sorry

def count_successful_sales (shoe_sizes : List Nat) (customer_requests : List (Nat × Nat)) : Nat :=
  sorry

def sum_request_prices (requests : List (Nat × Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem earnings_nonnegative
    (num_shoes : Nat) (shoe_sizes : List Nat) (customer_requests : List (Nat × Nat)) :
    calculate_shoe_shop_earnings num_shoes shoe_sizes customer_requests ≥ 0 :=
sorry

theorem earnings_upper_bound
    (num_shoes : Nat) (shoe_sizes : List Nat) (customer_requests : List (Nat × Nat)) :
    calculate_shoe_shop_earnings num_shoes shoe_sizes customer_requests ≤
    sum_request_prices customer_requests :=
sorry

theorem sales_limited_by_inventory
    (num_shoes : Nat) (shoe_sizes : List Nat) (customer_requests : List (Nat × Nat)) :
    count_successful_sales shoe_sizes customer_requests ≤ shoe_sizes.length :=
sorry

theorem empty_inventory_zero_earnings (requests : List (Nat × Nat)) :
    calculate_shoe_shop_earnings 0 [] requests = 0 :=
sorry

theorem inventory_order_invariant
    (num_shoes : Nat) (shoe_sizes : List Nat) (requests : List (Nat × Nat)) :
    calculate_shoe_shop_earnings num_shoes shoe_sizes requests =
    calculate_shoe_shop_earnings num_shoes shoe_sizes.reverse requests :=
sorry
-- </vc-theorems>