-- <vc-helpers>
-- </vc-helpers>

def fuelPrice (litres : Float) (price : Float) : Float :=
  sorry

theorem fuel_price_discount_steps (litres : Float) (price : Float)
  (h₁ : litres ≥ 0) (h₂ : litres ≤ 1000)
  (h₃ : price ≥ 0.25) (h₄ : price ≤ 100) :
  let maxDiscount := min ((Float.floor (litres/2)) * 0.05) 0.25
  let discountedPrice := price - maxDiscount
  fuelPrice litres price = discountedPrice * litres := sorry

/-
info: 212.5
-/
-- #guard_msgs in
-- #eval fuel_price 10 21.5

/-
info: 390
-/
-- #guard_msgs in
-- #eval fuel_price 40 10

/-
info: 83.7
-/
-- #guard_msgs in
-- #eval fuel_price 15 5.83

-- Apps difficulty: introductory
-- Assurance level: unguarded