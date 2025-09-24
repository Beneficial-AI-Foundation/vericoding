-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def excluding_vat_price (price : Int) : Float := sorry

theorem excluding_vat_price_nonnegative (price : Int) (h : price ≥ 0) :
  excluding_vat_price price ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem excluding_vat_price_less_than_input (price : Int) (h : price > 0) :
  excluding_vat_price price < (Float.ofInt price) := sorry

theorem excluding_vat_price_zero :
  excluding_vat_price 0 = 0 := sorry

theorem excluding_vat_price_example_115 :
  excluding_vat_price 115 = 100 := sorry

theorem excluding_vat_price_example_230 :
  excluding_vat_price 230 = 200 := sorry
-- </vc-theorems>