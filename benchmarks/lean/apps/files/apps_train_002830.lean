-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: 200.0
-/
-- #guard_msgs in
-- #eval excluding_vat_price 230.0

/-
info: 106.96
-/
-- #guard_msgs in
-- #eval excluding_vat_price 123

/-
info: -1
-/
-- #guard_msgs in
-- #eval excluding_vat_price None
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded