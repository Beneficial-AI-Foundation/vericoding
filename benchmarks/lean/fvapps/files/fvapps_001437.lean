-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numDigits (n : Nat) : Nat :=
  sorry

def maximizeStockPrice (n k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maximize_stock_price_properties (n k : Nat) (h1 : n ≤ 999999) (h2 : k ≤ 10) :
  let result := maximizeStockPrice n k;

  result ≥ n

  ∧ numDigits result = numDigits n

  ∧ ∃ changes, changes ≤ k

  ∧ (k = 0 → result = n) :=
sorry

theorem maximize_stock_price_saturated (n k : Nat) (h1 : k ≥ numDigits n) :
  let result := maximizeStockPrice n k;

  result = n :=
sorry

theorem maximize_stock_price_edge_cases :
  maximizeStockPrice 0 0 = 0
  ∧ maximizeStockPrice 1 1 = 9
  ∧ maximizeStockPrice 9 1 = 9
  ∧ maximizeStockPrice 99 1 = 99 :=
sorry
-- </vc-theorems>