-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_chocolates (n : Nat) (budget : Nat) (prices : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_chocolates_within_bounds (n : Nat) (budget : Nat) (prices : List Nat)
  (h1 : prices.length = n)
  (h2 : ∀ x ∈ prices, 1 ≤ x ∧ x ≤ 1000)
  (h3 : 1 ≤ budget ∧ budget ≤ 10000)
  (h4 : 1 ≤ n ∧ n ≤ 100) :
  0 ≤ max_chocolates n budget prices ∧ max_chocolates n budget prices ≤ n :=
  sorry

theorem max_chocolates_equals_count (n : Nat) (budget : Nat) (prices : List Nat)
  (h : prices.length = n) :
  ∃ (sorted_prices : List Nat), 
    sorted_prices.length = prices.length ∧
    (∀ i j : Nat, i < j → i < sorted_prices.length → j < sorted_prices.length →
      sorted_prices.get! i ≤ sorted_prices.get! j) ∧
    max_chocolates n budget prices = 
      let count := sorted_prices.foldl
        (fun (acc : Nat × Nat) (price : Nat) => 
          if price ≤ budget - acc.2
          then (acc.1 + 1, acc.2 + price)
          else acc)
        (0, 0)
      count.1 :=
  sorry

theorem max_chocolates_monotone_budget (n : Nat) (budget : Nat) (prices : List Nat)
  (h : prices.length = n)
  (h2 : ∀ x ∈ prices, 0 < x) :
  max_chocolates n budget prices ≤ max_chocolates n (budget + 1) prices :=
  sorry

theorem max_chocolates_zero_budget (n : Nat) (prices : List Nat)
  (h : prices.length = n)
  (h2 : ∀ x ∈ prices, 0 < x) :
  max_chocolates n 0 prices = 0 :=
  sorry
-- </vc-theorems>