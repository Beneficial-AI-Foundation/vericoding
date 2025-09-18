-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_total (subtotal tax tip : Float) : Float := sorry

def round (x : Float) (d : Int) : Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_total_zero_tax_tip (subtotal : Float) (h1 : 0.01 ≤ subtotal) (h2 : subtotal ≤ 1000000) :
  (calculate_total subtotal 0 0 - subtotal).abs < 0.01 := sorry

theorem calculate_total_components (subtotal tax tip : Float)
  (h1 : 0.01 ≤ subtotal) (h2 : subtotal ≤ 1000000)
  (h3 : 0 ≤ tax) (h4 : tax ≤ 100)
  (h5 : 0 ≤ tip) (h6 : tip ≤ 100) :
  let expected := subtotal + (subtotal * tax/100) + (subtotal * tip/100)
  (calculate_total subtotal tax tip - round expected 2).abs < 0.01 := sorry

theorem calculate_total_tax_component (subtotal tax tip : Float) 
  (h1 : 0.01 ≤ subtotal) (h2 : subtotal ≤ 1000000)
  (h3 : 0 ≤ tax) (h4 : tax ≤ 100)
  (h5 : 0 ≤ tip) (h6 : tip ≤ 100) :
  (calculate_total subtotal tax tip - (calculate_total subtotal 0 tip + (subtotal * tax/100))).abs < 0.01 := sorry

theorem calculate_total_tip_component (subtotal tax tip : Float)
  (h1 : 0.01 ≤ subtotal) (h2 : subtotal ≤ 1000000)
  (h3 : 0 ≤ tax) (h4 : tax ≤ 100)
  (h5 : 0 ≤ tip) (h6 : tip ≤ 100) :
  (calculate_total subtotal tax tip - (calculate_total subtotal tax 0 + (subtotal * tip/100))).abs < 0.01 := sorry
-- </vc-theorems>