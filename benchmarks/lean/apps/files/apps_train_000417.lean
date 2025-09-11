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

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_valid_delivery_orders 1

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_valid_delivery_orders 2

/-
info: 90
-/
-- #guard_msgs in
-- #eval count_valid_delivery_orders 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible