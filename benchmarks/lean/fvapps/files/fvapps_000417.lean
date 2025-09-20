-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def M := 10^9 + 7

def count_valid_delivery_orders (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_valid_delivery_orders_positive (n : Nat) 
  (h : n > 0) : 
  count_valid_delivery_orders n > 0 :=
  sorry

theorem count_valid_delivery_orders_base_case :
  count_valid_delivery_orders 1 = 1 :=
  sorry
-- </vc-theorems>