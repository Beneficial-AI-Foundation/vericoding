-- <vc-preamble>
def list_sum (xs: List Nat) : Nat :=
xs.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_operations_max_profit (customers: List Nat) (boarding_cost: Nat) (running_cost: Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_operations_result_valid
  (customers: List Nat)
  (boarding_cost: Nat)
  (running_cost: Nat)
  (h1: customers.length > 0)
  (h2: boarding_cost > 0)
  (h3: running_cost > 0)
  (h4: ∀ x ∈ customers, x ≤ 1000)
  : let result := min_operations_max_profit customers boarding_cost running_cost
    result = -1 ∨ result > 0 :=
sorry

theorem min_operations_max_rotations
  (customers: List Nat)
  (boarding_cost: Nat)
  (running_cost: Nat)
  (h1: customers.length > 0)
  (h2: boarding_cost > 0)
  (h3: running_cost > 0)
  (h4: ∀ x ∈ customers, x ≤ 1000)
  : let result := min_operations_max_profit customers boarding_cost running_cost
    let total := list_sum customers
    let max_rotations := total / 4 + (if total % 4 = 0 then 0 else 1)
    result = -1 ∨ result ≤ max_rotations + total :=
sorry

theorem high_running_cost_unprofitable
  (customers: List Nat)
  (boarding_cost: Nat)
  (h1: customers.length > 0)
  (h2: customers.length ≤ 10)
  (h3: boarding_cost > 0)
  (h4: boarding_cost ≤ 10)
  (h5: ∀ x ∈ customers, x ≤ 10)
  : min_operations_max_profit customers boarding_cost 1000 = -1 :=
sorry

theorem high_profit_scenario_profitable
  (customers: List Nat)
  (boarding_cost: Nat)
  (h1: customers.length > 0)
  (h2: boarding_cost ≥ 100)
  (h3: ∀ x ∈ customers, x ≥ 100 ∧ x ≤ 1000)
  : min_operations_max_profit customers boarding_cost 1 > 0 :=
sorry

theorem no_customers_unprofitable
  (customers: List Nat)
  (boarding_cost: Nat)
  (running_cost: Nat)
  (h1: customers.length > 0)
  (h2: boarding_cost > 0)
  (h3: running_cost > 0)
  (h4: ∀ x ∈ customers, x = 0)
  : min_operations_max_profit customers boarding_cost running_cost = -1 :=
sorry
-- </vc-theorems>