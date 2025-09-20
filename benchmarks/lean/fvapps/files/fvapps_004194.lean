-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mango (quantity price : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mango_cost_less_than_full : ∀ (quantity price : Nat),
  mango quantity price ≤ quantity * price :=
sorry

theorem mango_non_negative : ∀ (quantity price : Nat),
  mango quantity price ≥ 0 :=
sorry

theorem mango_every_third_free : ∀ (quantity price : Nat),
  mango quantity price = (quantity - quantity / 3) * price :=
sorry

theorem mango_zero_price : ∀ (quantity : Nat),
  mango quantity 0 = 0 :=
sorry

theorem mango_single_quantity : ∀ (price : Nat),
  mango 1 price = price :=
sorry
-- </vc-theorems>