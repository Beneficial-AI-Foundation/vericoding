-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def order (pizzas salads appetizers : Nat) : Nat := sorry

def ceil (n : Nat) (d : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem order_non_negative (pizzas salads appetizers : Nat) : 
  order pizzas salads appetizers ≥ 0 := sorry

theorem adding_pizzas_increases_time (pizzas : Nat) :
  order (pizzas + 1) 0 0 ≥ order pizzas 0 0 := sorry
-- </vc-theorems>