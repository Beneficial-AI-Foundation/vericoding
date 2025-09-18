-- <vc-preamble>
def max_profit (prices : List Nat) : Int := sorry

def maximum (l : List Nat) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minimum (l : List Nat) : Nat := sorry

theorem max_profit_bounds {prices : List Nat} (h : prices.length ≥ 2) : 
  max_profit prices ≤ (maximum prices) - (minimum prices) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ascending_max_profit {prices : List Nat} (h : prices.length ≥ 2) 
  (ascending : ∀ (i : Nat), i + 1 < prices.length → prices[i]! ≤ prices[i + 1]!) :
  max_profit prices = prices.getLast! - prices.head! := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval max_profit [10, 7, 5, 8, 11, 9]

/-
info: 1
-/
-- #guard_msgs in
-- #eval max_profit [3, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval max_profit [9, 9]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded