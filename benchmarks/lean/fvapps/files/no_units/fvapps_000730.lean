-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_cable_cost (n : Nat) (costs : List (List Nat)) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_cable_cost_le_total_cost (n : Nat) (costs : List (List Nat)) 
  (h_costs_len : costs.length = n)
  (h_costs_inner : ∀ i : Fin n, (costs[i.val]).length = n) :
  min_cable_cost n costs ≤ costs.foldr (λ row acc => row.foldr (λ x s => x + s) 0 + acc) 0 / 2 :=
sorry

theorem min_cable_cost_le_max_edges (n : Nat) (costs : List (List Nat))
  (h_costs_len : costs.length = n)
  (h_costs_inner : ∀ i : Fin n, (costs[i.val]).length = n) :
  min_cable_cost n costs ≤ 
    (n * (n-1)) / 2 * 
    (costs.foldr (λ row acc => max acc (row.foldr max 0)) 0) :=
sorry
-- </vc-theorems>