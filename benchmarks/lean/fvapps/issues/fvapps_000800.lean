-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_gift_cost (n m : Nat) (color_prices : List (Nat × Nat)) : Nat := sorry

theorem gift_cost_positive (n m : Nat) (color_prices : List (Nat × Nat)) :
  calc_gift_cost n m color_prices > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gift_cost_bounded (n m : Nat) (color_prices : List (Nat × Nat)) 
  (h1 : color_prices ≠ []) :
  let prices := List.map Prod.snd color_prices
  calc_gift_cost n m color_prices ≥ (List.minimum? prices).getD 0 ∧ 
  calc_gift_cost n m color_prices ≤ ((List.maximum? prices).getD 0) * color_prices.length 
  := sorry

theorem gift_cost_monotonic (n m : Nat) (color_prices : List (Nat × Nat))
  (h : m > 1) :
  calc_gift_cost n m color_prices ≥ 
  calc_gift_cost n (m-1) color_prices := sorry

theorem gift_cost_single_color :
  calc_gift_cost 1 1 [(1, 10)] = 10 := sorry

theorem gift_cost_duplicate_color :
  calc_gift_cost 2 1 [(1, 5), (1, 5)] = 7 := sorry
-- </vc-theorems>