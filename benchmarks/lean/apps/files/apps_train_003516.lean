/-
The pizza store wants to know how long each order will take. They know:

- Prepping a pizza takes 3 mins
- Cook a pizza takes 10 mins
- Every salad takes 3 mins to make
- Every appetizer takes 5 mins to make
- There are 2 pizza ovens
- 5 pizzas can fit in a oven
- Prepping for a pizza must be done before it can be put in the oven
- There are two pizza chefs and one chef for appitizers and salads combined
- The two pizza chefs can work on the same pizza

Write a function, order, which will tell the company how much time the order will take.

See example tests for details.
-/

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