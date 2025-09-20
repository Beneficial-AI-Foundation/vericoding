-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_profit_assignment (difficulty profit worker : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_profit_basic_properties
  (difficulty : List Int) 
  (profit : List Int)
  (worker : List Int)
  (hdiff : ∀ d ∈ difficulty, 1 ≤ d ∧ d ≤ 20)
  (hprof : ∀ p ∈ profit, 1 ≤ p ∧ p ≤ 100)
  (hwork : ∀ w ∈ worker, 1 ≤ w ∧ w ≤ 20)
  (hlen : difficulty.length = profit.length)
  : let result := max_profit_assignment difficulty profit worker
    result ≥ 0 ∧ result ≤ (List.foldl max 0 profit) * worker.length :=
  sorry

theorem zero_skill_workers_result
  (difficulty : List Int)
  (profit : List Int)
  (worker : List Int)
  (hdiff : ∀ d ∈ difficulty, 1 ≤ d ∧ d ≤ 10)
  (hprof : ∀ p ∈ profit, 0 ≤ p ∧ p ≤ 10)
  (hwork : ∀ w ∈ worker, w = 0)
  (hlen : difficulty.length = profit.length)
  : max_profit_assignment difficulty profit worker = 0 :=
  sorry

theorem overskilled_workers_result
  (difficulty : List Int)
  (profit : List Int)
  (worker : List Int)
  (hdiff : ∀ d ∈ difficulty, 1 ≤ d ∧ d ≤ 10)
  (hprof : ∀ p ∈ profit, 0 ≤ p ∧ p ≤ 100)
  (hwork : ∀ w ∈ worker, 100 ≤ w ∧ w ≤ 200)
  (hlen : difficulty.length = profit.length)
  : max_profit_assignment difficulty profit worker = worker.length * (List.foldl max 0 profit) :=
  sorry
-- </vc-theorems>