-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minCostTickets (days : List Nat) (costs : List Nat) : Nat := sorry

theorem min_cost_tickets_cost_bounds
  (days : List Nat)
  (costs : List Nat)
  (h1 : days.length > 0)
  (h2 : costs.length = 3)
  (h3 : ∀ d ∈ days, d ≥ 1 ∧ d ≤ 365)
  (h4 : ∀ c ∈ costs, c ≥ 1 ∧ c ≤ 1000)
  (h5 : days.Nodup)
  : let result := minCostTickets days costs
    result ≥ min (costs[0]!) (min (costs[1]!/7) (costs[2]!/30)) * days.length ∧
    result ≤ costs[0]! * days.length :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem weekly_window_cost
  (days : List Nat)
  (costs : List Nat)
  (h1 : days.length > 0)
  (h2 : costs.length = 3)
  (h3 : ∀ d ∈ days, d ≥ 1 ∧ d ≤ 7)
  (h4 : ∀ c ∈ costs, c ≥ 1 ∧ c ≤ 1000)
  (h5 : days.Nodup) :
  minCostTickets days costs ≤ min costs[1]! (costs[0]! * days.length) :=
  sorry

theorem consecutive_days_cost
  (costs : List Nat)
  (days : List Nat)
  (h1 : costs.length = 3)
  (h2 : days = List.range 7)
  (h3 : ∀ c ∈ costs, c ≥ 1 ∧ c ≤ 1000) :
  minCostTickets days costs = min (costs[0]! * 7) (min costs[1]! costs[2]!) :=
  sorry
-- </vc-theorems>