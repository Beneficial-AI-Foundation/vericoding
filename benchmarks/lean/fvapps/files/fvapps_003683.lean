-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.toFloat (s : String) : Option Float :=
sorry

def List.sort (l : List Float) (lt : Float → Float → Bool) : List Float := sorry

def search (budget : Float) (prices : List Float) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem search_sorted (budget : Float) (prices : List Float)
  (h1 : budget ≥ 0) (h2 : budget ≤ 1000)
  (h3 : ∀ x ∈ prices, x ≥ 0 ∧ x ≤ 1000)
  (h4 : prices ≠ []) :
  let result := search budget prices
  let nums := (result.splitOn ",").filterMap String.toFloat
  ∀ i, i < nums.length - 1 → nums[i]! ≤ nums[i+1]! :=
sorry

theorem search_within_budget (budget : Float) (prices : List Float)
  (h1 : budget ≥ 0) (h2 : budget ≤ 1000)
  (h3 : ∀ x ∈ prices, x ≥ 0 ∧ x ≤ 1000)
  (h4 : prices ≠ []) :
  let result := search budget prices
  let nums := (result.splitOn ",").filterMap String.toFloat
  ∀ x ∈ nums, x ≤ budget :=
sorry

theorem search_includes_all_eligible (budget : Float) (prices : List Float)
  (h1 : budget ≥ 0) (h2 : budget ≤ 1000)
  (h3 : ∀ x ∈ prices, x ≥ 0 ∧ x ≤ 1000)
  (h4 : prices ≠ []) :
  let eligible := List.sort (prices.filter (· ≤ budget)) (·≤·)
  let result := search budget prices
  result = String.intercalate "," (eligible.map toString) :=
sorry

theorem search_zero_budget (prices : List Float)
  (h1 : ∀ x ∈ prices, x ≥ 0)
  (h2 : prices ≠ []) :
  let eligible := List.sort (prices.filter (·≤ 0)) (·≤·)
  search 0 prices = String.intercalate "," (eligible.map toString) :=
sorry
-- </vc-theorems>