-- <vc-helpers>
-- </vc-helpers>

def order (pizzas salads appetizers : Nat) : Nat := sorry

def ceil (n : Nat) (d : Nat) : Nat := sorry

theorem order_non_negative (pizzas salads appetizers : Nat) : 
  order pizzas salads appetizers ≥ 0 := sorry

theorem adding_pizzas_increases_time (pizzas : Nat) :
  order (pizzas + 1) 0 0 ≥ order pizzas 0 0 := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible