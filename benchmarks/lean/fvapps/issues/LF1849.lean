-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Cashier.getBill (c: Cashier) (selected_products: List Nat) (amounts: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cashier_initialization_n {n disc prods prices : Nat} (c : Cashier) :
  c.n = n → c.n > 0 :=
sorry

theorem cashier_initialization_discount {n disc prods prices: Nat} (c : Cashier) :
  c.discount = disc → c.discount ≥ 0 ∧ c.discount ≤ 100 :=
sorry

theorem cashier_products_nonempty {n disc : Nat} {prods prices : List Nat} (c : Cashier) :
  c.products.length > 0 :=
sorry

theorem bill_nonnegative {n disc : Nat} {prods prices selected amounts : List Nat} (c : Cashier) :
  c.getBill selected amounts ≥ 0 := 
sorry
-- </vc-theorems>