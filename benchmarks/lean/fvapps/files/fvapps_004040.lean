-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_tip (price : Int) (rating : Int) : Int := sorry

theorem tip_always_non_negative (price : Int) (rating : Int) 
  (h₁ : price ≥ 0) (h₂ : price ≤ 10000) (h₃ : rating ≥ -1) (h₄ : rating ≤ 1) : 
  calc_tip price rating ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem higher_rating_higher_tip_1 (price : Int) 
  (h₁ : price ≥ 0) (h₂ : price ≤ 10000) :
  calc_tip price 1 ≥ calc_tip price 0 := sorry

theorem higher_rating_higher_tip_2 (price : Int)
  (h₁ : price ≥ 0) (h₂ : price ≤ 10000) :
  calc_tip price 0 ≥ calc_tip price (-1) := sorry

theorem tip_scales_with_price (price : Int) (rating : Int)
  (h₁ : price > 100) (h₂ : price ≤ 10000) (h₃ : rating ≥ -1) (h₄ : rating ≤ 1) :
  calc_tip price rating ≥ calc_tip (price / 2) rating := sorry

theorem tip_rounding_consistency (price : Int) (h₁ : price ≥ 0) (h₂ : price ≤ 1000) :
  let rounded_down := calc_tip (price - (price % 10)) 0
  let rounded_up := calc_tip (price + (10 - price % 10)) 0
  let actual := calc_tip price 0
  actual = rounded_down ∨ actual = rounded_up := sorry
-- </vc-theorems>