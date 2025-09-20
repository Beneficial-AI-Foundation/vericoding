-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_profit (prices : List Nat) : Int :=
sorry

def maximum (l : List Nat) : Nat :=
sorry

def minimum (l : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_profit_bounds {prices : List Nat} (h : prices.length ≥ 2) :
  max_profit prices ≤ (maximum prices) - (minimum prices) :=
sorry

theorem ascending_max_profit {prices : List Nat} (h : prices.length ≥ 2)
  (ascending : ∀ (i : Nat), i + 1 < prices.length → prices[i]! ≤ prices[i + 1]!) :
  max_profit prices = prices.getLast! - prices.head! :=
sorry
-- </vc-theorems>