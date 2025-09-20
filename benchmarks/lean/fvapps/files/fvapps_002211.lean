-- <vc-preamble>
def sum_list : List Nat → Nat
  | [] => 0
  | h::t => h + sum_list t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_cost_to_cut_trees (n : Nat) (heights : List Nat) (costs : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_cost_non_negative (n : Nat) (heights : List Nat) (costs : List Nat)
  (h1 : n ≥ 2)
  (h2 : heights.length = n)
  (h3 : costs.length = n)
  (h4 : ∀ h ∈ heights, h ≥ 1 ∧ h ≤ 1000)
  (h5 : ∀ c ∈ costs, c ≤ 1000)
  (h6 : costs.head! > costs.getLast!) :
  min_cost_to_cut_trees n heights costs ≥ 0 :=
sorry

theorem min_cost_upper_bound (n : Nat) (heights : List Nat) (costs : List Nat)
  (h1 : n ≥ 2)
  (h2 : heights.length = n)
  (h3 : costs.length = n)
  (h4 : ∀ h ∈ heights, h ≥ 1 ∧ h ≤ 1000)
  (h5 : ∀ c ∈ costs, c ≤ 1000)
  (h6 : costs.head! > costs.getLast!) :
  min_cost_to_cut_trees n heights costs ≤ sum_list (heights.map (· * costs.head!)) :=
sorry

theorem min_cost_last_worker_bound (heights : List Nat) (costs : List Nat)
  (h1 : heights.length ≥ 2)
  (h2 : ∀ h ∈ heights, h ≥ 1 ∧ h ≤ 100)
  (h3 : costs.length = heights.length)
  (h4 : ∀ c ∈ costs, c ≤ 100)
  (h5 : costs.head! > costs.getLast!) :
  min_cost_to_cut_trees heights.length heights costs ≥ heights.getLast! * costs.getLast! :=
sorry
-- </vc-theorems>