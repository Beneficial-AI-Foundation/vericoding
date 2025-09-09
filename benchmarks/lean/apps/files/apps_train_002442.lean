def calculate_shoe_shop_earnings (num_shoes : Nat) (shoe_sizes : List Nat) 
    (customer_requests : List (Nat × Nat)) : Nat :=
  sorry

def count_successful_sales (shoe_sizes : List Nat) (customer_requests : List (Nat × Nat)) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def sum_request_prices (requests : List (Nat × Nat)) : Nat :=
  sorry

-- Earnings cannot be negative (this is implied by Nat return type)

theorem earnings_nonnegative
    (num_shoes : Nat) (shoe_sizes : List Nat) (customer_requests : List (Nat × Nat)) :
    calculate_shoe_shop_earnings num_shoes shoe_sizes customer_requests ≥ 0 := sorry

-- Earnings cannot exceed sum of requested prices

theorem earnings_upper_bound
    (num_shoes : Nat) (shoe_sizes : List Nat) (customer_requests : List (Nat × Nat)) :
    calculate_shoe_shop_earnings num_shoes shoe_sizes customer_requests ≤ 
    sum_request_prices customer_requests := sorry

-- Cannot sell more shoes than inventory

theorem sales_limited_by_inventory
    (num_shoes : Nat) (shoe_sizes : List Nat) (customer_requests : List (Nat × Nat)) :
    count_successful_sales shoe_sizes customer_requests ≤ shoe_sizes.length := sorry

-- Empty inventory yields zero earnings

theorem empty_inventory_zero_earnings (requests : List (Nat × Nat)) :
    calculate_shoe_shop_earnings 0 [] requests = 0 := sorry

-- Order of inventory doesn't affect earnings

theorem inventory_order_invariant
    (num_shoes : Nat) (shoe_sizes : List Nat) (requests : List (Nat × Nat)) :
    calculate_shoe_shop_earnings num_shoes shoe_sizes requests = 
    calculate_shoe_shop_earnings num_shoes shoe_sizes.reverse requests := sorry

/-
info: 200
-/
-- #guard_msgs in
-- #eval calculate_shoe_shop_earnings 10 [2, 3, 4, 5, 6, 8, 7, 6, 5, 18] [(6, 55), (6, 45), (6, 55), (4, 40), (18, 60), (10, 50)]

/-
info: 0
-/
-- #guard_msgs in
-- #eval calculate_shoe_shop_earnings 0 [] [(6, 55)]

/-
info: 0
-/
-- #guard_msgs in
-- #eval calculate_shoe_shop_earnings 1 [2] [(3, 50)]

-- Apps difficulty: introductory
-- Assurance level: guarded