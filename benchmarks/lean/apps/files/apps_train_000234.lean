-- <vc-helpers>
-- </vc-helpers>

def maxProfit (prices: List Nat) : Nat :=
  sorry

-- Maximum profit should be non-negative for any non-empty price list

theorem maxprofit_non_negative {prices: List Nat} (h: prices ≠ []) : 
  maxProfit prices ≥ 0 :=
  sorry

-- Descending prices should give zero profit 

theorem maxprofit_descending {prices: List Nat} (h: prices ≠ []) 
  (hsorted: ∀ i j, i < j → j < prices.length → prices[i]! ≥ prices[j]!) :
  maxProfit prices = 0 :=
  sorry

-- For ascending prices, profit should be max of single or double transaction

theorem maxprofit_ascending {prices: List Nat} (h: prices ≠ [])
  (hsorted: ∀ i j, i < j → j < prices.length → prices[i]! ≤ prices[j]!)
  (hlen: prices.length ≥ 4) :
  maxProfit prices = min 
    (prices[prices.length-1]! - prices[0]!)
    ((prices[prices.length-1]! - prices[0]!) + (prices[prices.length-2]! - prices[1]!)) :=
  sorry

-- Single transaction case for ascending prices

theorem maxprofit_ascending_single {prices: List Nat} (h: prices ≠ [])
  (hsorted: ∀ i j, i < j → j < prices.length → prices[i]! ≤ prices[j]!)
  (hlen1: prices.length ≥ 2) (hlen2: prices.length < 4) :
  maxProfit prices = prices[prices.length-1]! - prices[0]! :=
  sorry

-- Constant prices should give zero profit

theorem maxprofit_constant {prices: List Nat} (h: prices ≠ [])
  (hconst: ∀ i j, i < prices.length → j < prices.length → prices[i]! = prices[j]!) :
  maxProfit prices = 0 :=
  sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval maxProfit [3, 3, 5, 0, 0, 3, 1, 4]

/-
info: 4
-/
-- #guard_msgs in
-- #eval maxProfit [1, 2, 3, 4, 5]

/-
info: 0
-/
-- #guard_msgs in
-- #eval maxProfit [7, 6, 4, 3, 1]

-- Apps difficulty: interview
-- Assurance level: unguarded