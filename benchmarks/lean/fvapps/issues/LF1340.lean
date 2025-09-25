-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxRestaurantCustomers (testCases : List (List Cell)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_customers_single_case
  (n k : Nat)
  (cells : List Cell)
  (h1 : n ≥ 1)
  (h2 : k ≥ 1) 
  (h3 : cells.length ≥ 1)
  (h4 : ∀ c ∈ cells, c.start < c.finish)
  (h5 : ∀ c ∈ cells, c.capacity ≤ k) :
  let result := maxRestaurantCustomers [cells]
  result.head! ≤ cells.length ∧ 
  result.head! ≤ k * n :=
sorry

theorem max_customers_multiple_cases
  (testCases : List (List Cell))
  (h1 : testCases.length ≥ 1)
  (h2 : ∀ case ∈ testCases, case.length ≥ 1)
  (h3 : ∀ case ∈ testCases, ∀ c ∈ case, c.start < c.finish)
  (h4 : ∀ case ∈ testCases, ∀ c ∈ case, c.capacity ≤ k) :
  let results := maxRestaurantCustomers testCases
  results.length = testCases.length ∧
  ∀ i < results.length, 
    results[i]! ≤ testCases[i]!.length ∧
    results[i]! ≤ k * n :=
sorry

/-
info: [3]
-/
-- #guard_msgs in
-- #eval max_restaurant_customers [test1]

/-
info: [3]
-/
-- #guard_msgs in
-- #eval max_restaurant_customers [test2]

/-
info: [3, 3]
-/
-- #guard_msgs in
-- #eval max_restaurant_customers [test1, test2]
-- </vc-theorems>