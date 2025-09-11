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

/-
info: 110
-/
-- #guard_msgs in
-- #eval min_cost_two_cities [[10, 20], [30, 200], [400, 50], [30, 20]]

/-
info: 1859
-/
-- #guard_msgs in
-- #eval min_cost_two_cities [[259, 770], [448, 54], [926, 667], [184, 139], [840, 118], [577, 469]]

/-
info: 3086
-/
-- #guard_msgs in
-- #eval min_cost_two_cities [[515, 563], [451, 713], [537, 709], [343, 819], [855, 779], [457, 60], [650, 359], [631, 42]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded