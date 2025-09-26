-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_cost_two_cities (costs: List (List Nat)) : Nat := sorry

def sum_all_costs (costs: List (List Nat)) : Nat :=
  costs.foldl (fun acc row => acc + row.foldl (· + ·) 0) 0
-- </vc-definitions>

-- <vc-theorems>
theorem min_cost_two_cities_is_nonnegative 
  (costs: List (List Nat))
  (h1: costs.length % 2 = 0)
  (h2: ∀ cost ∈ costs, cost.length = 2) :
  min_cost_two_cities costs ≥ 0 := sorry

theorem min_cost_two_cities_upper_bound
  (costs: List (List Nat)) 
  (h1: costs.length % 2 = 0)
  (h2: ∀ cost ∈ costs, cost.length = 2) :
  min_cost_two_cities costs ≤ sum_all_costs costs := sorry

theorem min_cost_two_cities_swap_invariant
  (costs: List (List Nat))
  (h1: costs.length % 2 = 0) 
  (h2: ∀ cost ∈ costs, cost.length = 2) :
  min_cost_two_cities costs = 
  min_cost_two_cities (costs.map (fun cost => [cost.get! 1, cost.get! 0])) := sorry
-- </vc-theorems>