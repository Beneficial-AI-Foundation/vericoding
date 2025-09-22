-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_cost (n : Nat) (cuts : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_cost_nonnegative (n : Nat) (cuts : List Nat) (h : n ≥ 2) :
  min_cost n cuts ≥ 0 :=
sorry

theorem min_cost_empty (n : Nat) (cuts : List Nat) (h : n ≥ 2) :
  (∀ c ∈ cuts, ¬(0 < c ∧ c < n)) → min_cost n cuts = 0 :=
sorry

theorem min_cost_upper_bound (n : Nat) (cuts : List Nat) (h : n ≥ 2) :
  let valid_cuts := cuts.filter (fun c => 0 < c ∧ c < n)
  min_cost n cuts ≤ n * valid_cuts.length :=
sorry

theorem min_cost_order_independent (n : Nat) (cuts : List Nat) (h : n ≥ 2) :
  let valid_cuts := cuts.filter (fun c => 0 < c ∧ c < n)
  min_cost n cuts = min_cost n valid_cuts.reverse :=
sorry

theorem min_cost_single_middle_cut (n : Nat) (h : n > 2) :
  min_cost n [n / 2] = n :=
sorry
-- </vc-theorems>